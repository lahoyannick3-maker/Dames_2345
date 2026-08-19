/* ==========================================================
   moteur.c — Portage en C du moteur IA du jeu de Dames
   ==========================================================
   Portage FIDÈLE des fonctions JS suivantes (aucune logique
   modifiée, juste traduite) :
     clonerPlateau, dansPlateau, getCoupsPion, getCoupsDame,
     getTousLesCoups, getTousLesCoupsPour, genererClePlateau,
     evaluerPlateau, minimax, quiescence, appliquerCoupSimule

   Représentation du plateau :
     couleur = -1  -> case vide (ou non jouable)
     couleur =  0  -> pion/dame BLANC
     couleur =  1  -> pion/dame NOIR
   ========================================================== */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>

#ifdef __EMSCRIPTEN__
#include <emscripten/emscripten.h>
#else
#define EMSCRIPTEN_KEEPALIVE
#endif

#define TAILLE 10
#define BLANC 0
#define NOIR 1
#define VIDE (-1)

typedef struct {
    int8_t couleur;   /* BLANC, NOIR, ou VIDE */
    int8_t estDame;
} Case;

typedef Case Plateau[TAILLE][TAILLE];

static const double MATRICE_TACTIQUE[TAILLE][TAILLE] = {
    {1.4, 1.2, 1.2, 1.2, 1.2, 1.2, 1.2, 1.2, 1.2, 1.4},
    {1.1, 1.3, 1.1, 1.1, 1.1, 1.1, 1.1, 1.1, 1.3, 1.1},
    {1.1, 1.1, 1.3, 1.2, 1.2, 1.2, 1.2, 1.3, 1.1, 1.1},
    {1.1, 1.1, 1.2, 1.5, 1.4, 1.4, 1.5, 1.2, 1.1, 1.1},
    {1.1, 1.1, 1.2, 1.4, 1.6, 1.6, 1.4, 1.2, 1.1, 1.1},
    {1.1, 1.1, 1.2, 1.4, 1.6, 1.6, 1.4, 1.2, 1.1, 1.1},
    {1.1, 1.1, 1.2, 1.5, 1.4, 1.4, 1.5, 1.2, 1.1, 1.1},
    {1.1, 1.1, 1.3, 1.2, 1.2, 1.2, 1.2, 1.3, 1.1, 1.1},
    {1.1, 1.3, 1.1, 1.1, 1.1, 1.1, 1.1, 1.1, 1.3, 1.1},
    {1.4, 1.2, 1.2, 1.2, 1.2, 1.2, 1.2, 1.2, 1.2, 1.4}
};

static int couleurHumain = BLANC; /* équivalent de la variable globale JS */

/* ---------- Coup : équivalent de l'objet JS {x, z, prise, pionPris, nbPrises} ---------- */
typedef struct {
    int x, z;
    int prise;
    int px, pz;     /* pion pris (si prise) */
    int nbPrises;
} Coup;

/* Coup complet, équivalent de {x1,z1,x2,z2,info} dans getTousLesCoupsPour */
typedef struct {
    int x1, z1, x2, z2;
    Coup info;
} CoupComplet;

#define MAX_COUPS 64

static int dansPlateau(int x, int z) {
    return x >= 0 && x < TAILLE && z >= 0 && z < TAILLE;
}

static void clonerPlateau(Plateau src, Plateau dst) {
    memcpy(dst, src, sizeof(Plateau));
}

/* ---------- getCoupsPion : équivalent JS getCoupsPion ---------- */
static int getCoupsPion(int x, int z, Plateau plat, Coup out[MAX_COUPS]) {
    int n = 0;
    Case pion = plat[x][z];
    if (pion.couleur == VIDE) return 0;
    int dir = (pion.couleur == BLANC) ? -1 : 1;

    int dxs[2] = {-1, 1};
    for (int i = 0; i < 2; i++) {
        int dx = dxs[i];
        int nx = x + dx, nz = z + dir;
        if (dansPlateau(nx, nz) && plat[nx][nz].couleur == VIDE) {
            out[n++] = (Coup){ .x = nx, .z = nz, .prise = 0 };
        }
    }
    for (int i = 0; i < 2; i++) {
        for (int j = 0; j < 2; j++) {
            int dx = dxs[i], dz = dxs[j];
            int nx = x + dx, nz = z + dz;
            int nx2 = x + 2 * dx, nz2 = z + 2 * dz;
            if (dansPlateau(nx2, nz2) && plat[nx2][nz2].couleur == VIDE &&
                plat[nx][nz].couleur != VIDE &&
                plat[nx][nz].couleur != pion.couleur) {
                out[n++] = (Coup){ .x = nx2, .z = nz2, .prise = 1, .px = nx, .pz = nz };
            }
        }
    }
    return n;
}

/* ---------- getCoupsDame : équivalent JS getCoupsDame ---------- */
static int getCoupsDame(int x, int z, Plateau plat, Coup out[MAX_COUPS]) {
    int n = 0;
    Case pion = plat[x][z];
    int dirs[4][2] = {{1,1},{1,-1},{-1,1},{-1,-1}};

    for (int d = 0; d < 4; d++) {
        int dx = dirs[d][0], dz = dirs[d][1];
        int nx = x + dx, nz = z + dz;
        int aPionRencontre = 0, prx = 0, prz = 0;
        while (dansPlateau(nx, nz)) {
            if (plat[nx][nz].couleur == VIDE) {
                if (!aPionRencontre) {
                    out[n++] = (Coup){ .x = nx, .z = nz, .prise = 0 };
                } else {
                    out[n++] = (Coup){ .x = nx, .z = nz, .prise = 1, .px = prx, .pz = prz };
                }
            } else if (plat[nx][nz].couleur == pion.couleur) {
                break;
            } else {
                if (aPionRencontre) break;
                aPionRencontre = 1; prx = nx; prz = nz;
            }
            nx += dx; nz += dz;
        }
    }
    return n;
}

/* ---------- getTousLesCoups : équivalent JS getTousLesCoups (calcule nbPrises via récursion) ---------- */
static int getTousLesCoups(int x, int z, Plateau plat, Coup out[MAX_COUPS]) {
    Case pion = plat[x][z];
    if (pion.couleur == VIDE) return 0;

    Coup bruts[MAX_COUPS];
    int nBruts = pion.estDame ? getCoupsDame(x, z, plat, bruts) : getCoupsPion(x, z, plat, bruts);

    int n = 0;
    for (int i = 0; i < nBruts; i++) {
        Coup c = bruts[i];
        if (!c.prise) {
            c.nbPrises = 0;
            out[n++] = c;
            continue;
        }
        Plateau temp;
        clonerPlateau(plat, temp);
        temp[c.x][c.z] = temp[x][z];
        temp[x][z] = (Case){ VIDE, 0 };
        temp[c.px][c.pz] = (Case){ VIDE, 0 };

        Coup chaines[MAX_COUPS];
        int nChaines = getTousLesCoups(c.x, c.z, temp, chaines);
        int maxChaine = 0;
        int auMoinsUnePrise = 0;
        for (int k = 0; k < nChaines; k++) {
            if (chaines[k].prise) {
                auMoinsUnePrise = 1;
                if (chaines[k].nbPrises > maxChaine) maxChaine = chaines[k].nbPrises;
            }
        }
        c.nbPrises = 1 + (auMoinsUnePrise ? maxChaine : 0);
        out[n++] = c;
    }
    return n;
}

/* ---------- getTousLesCoupsPour : équivalent JS getTousLesCoupsPour ---------- */
#define MAX_COUPS_TOTAL 512
static int getTousLesCoupsPour(int couleur, Plateau plat, CoupComplet out[MAX_COUPS_TOTAL]) {
    CoupComplet tous[MAX_COUPS_TOTAL];
    int nTous = 0;
    int aUnePrise = 0;

    for (int x = 0; x < TAILLE; x++) {
        for (int z = 0; z < TAILLE; z++) {
            Case pion = plat[x][z];
            if (pion.couleur == couleur) {
                Coup coups[MAX_COUPS];
                int nc = getTousLesCoups(x, z, plat, coups);
                for (int i = 0; i < nc; i++) {
                    if (coups[i].prise) aUnePrise = 1;
                    tous[nTous++] = (CoupComplet){ .x1 = x, .z1 = z, .x2 = coups[i].x, .z2 = coups[i].z, .info = coups[i] };
                }
            }
        }
    }

    /* Règle du bouffe maximum : si des prises existent, seules celles qui
       capturent le plus grand nombre de pièces sont autorisées (comme côté
       JS pour le joueur humain, cf. filtre sur maxPrises dans index.html).
       Sans ce filtre, l'IA pouvait choisir une prise de 1 alors qu'une
       prise de 2 (ou plus) était disponible, ce qui est illégal. */
    int maxPrises = 0;
    if (aUnePrise) {
        for (int i = 0; i < nTous; i++) {
            if (tous[i].info.prise && tous[i].info.nbPrises > maxPrises) {
                maxPrises = tous[i].info.nbPrises;
            }
        }
    }

    int n = 0;
    for (int i = 0; i < nTous; i++) {
        if (!aUnePrise) {
            out[n++] = tous[i];
        } else if (tous[i].info.prise && tous[i].info.nbPrises == maxPrises) {
            out[n++] = tous[i];
        }
    }
    return n;
}

/* ---------- genererClePlateau : équivalent JS genererClePlateau ---------- */
static void genererClePlateau(Plateau plat, char *out, size_t outSize) {
    out[0] = '\0';
    size_t pos = 0;
    for (int x = 0; x < TAILLE; x++) {
        for (int z = 0; z < TAILLE; z++) {
            Case p = plat[x][z];
            if (p.couleur != VIDE) {
                int written = snprintf(out + pos, outSize - pos, "%d%d%c%c|",
                                        x, z, p.couleur == BLANC ? 'b' : 'n', p.estDame ? 'D' : 'P');
                if (written > 0) pos += (size_t)written;
            }
        }
    }
}

/* ---------- evaluerPlateau : équivalent JS evaluerPlateau ---------- */
static double evaluerPlateau(Plateau plat) {
    int couleurIA = (couleurHumain == BLANC) ? NOIR : BLANC;
    double score = 0;
    int totalPions = 0;

    for (int x = 0; x < TAILLE; x++)
        for (int z = 0; z < TAILLE; z++)
            if (plat[x][z].couleur != VIDE) totalPions++;

    int estFinDePartie = totalPions <= 7;

    for (int x = 0; x < TAILLE; x++) {
        for (int z = 0; z < TAILLE; z++) {
            Case p = plat[x][z];
            if (p.couleur == VIDE) continue;

            double valeur = 0;
            if (p.estDame) {
                valeur = estFinDePartie ? 3800 : 3200;
                double distCentre = fabs(x - 4.5) + fabs(z - 4.5);
                valeur += (9 - distCentre) * 20;
            } else {
                valeur = 1000;
                valeur += MATRICE_TACTIQUE[x][z] * 100;
                double avance = (p.couleur == NOIR) ? z : (9 - z);
                valeur += avance * 40;
            }

            if (x == 0 || x == 9) valeur += 45;

            if (!estFinDePartie) {
                if (p.couleur == NOIR && z == 0) valeur += 90;
                if (p.couleur == BLANC && z == 9) valeur += 90;
            }

            int dir = (p.couleur == NOIR) ? -1 : 1;
            if (dansPlateau(x - 1, z + dir) && plat[x - 1][z + dir].couleur == p.couleur) valeur += 25;
            if (dansPlateau(x + 1, z + dir) && plat[x + 1][z + dir].couleur == p.couleur) valeur += 25;

            score += (p.couleur == couleurIA) ? valeur : -valeur;
        }
    }
    return score;
}

/* ---------- appliquerCoupSimule : équivalent JS appliquerCoupSimule ---------- */
static void appliquerCoupSimule(CoupComplet coup, Plateau plat) {
    Case pionOrigine = plat[coup.x1][coup.z1];
    if (pionOrigine.couleur == VIDE) return;

    plat[coup.x2][coup.z2] = (Case){ pionOrigine.couleur, pionOrigine.estDame };
    plat[coup.x1][coup.z1] = (Case){ VIDE, 0 };

    if (coup.info.prise) {
        plat[coup.info.px][coup.info.pz] = (Case){ VIDE, 0 };
    }

    if (plat[coup.x2][coup.z2].couleur == BLANC && coup.z2 == 0) plat[coup.x2][coup.z2].estDame = 1;
    if (plat[coup.x2][coup.z2].couleur == NOIR && coup.z2 == 9) plat[coup.x2][coup.z2].estDame = 1;
}

/* ---------- Table de transposition : équivalent de l'objet JS tableTransposition ----------
   Auparavant : chaînage avec malloc() par entrée, taille illimitée pendant une
   recherche. Avec ALLOW_MEMORY_GROWTH=1, le tas WASM grandissait à chaque
   recherche profonde (Expert) et ne redescendait jamais, même après
   tableTranspositionReset() — free() rend la mémoire à l'allocateur interne
   du module WASM, pas à l'OS/au navigateur.
   Maintenant : tableau statique à adressage direct (une seule case par
   bucket, pas de chaînage). Alloué une fois pour toutes au chargement du
   module, taille fixe pour toute la durée de vie du Worker -> l'empreinte
   mémoire ne bouge plus jamais, quel que soit le nombre de recherches. En
   cas de collision de hash, l'entrée précédente est simplement écrasée
   (compromis classique : légèrement moins de hits sur le cache, mais aucun
   risque de renvoyer un score faux car la clé est toujours revérifiée). */
typedef struct {
    char cle[300];
    double score;
    int profondeur;
    int occupee; /* 0 = case vide, 1 = utilisée */
} TTEntree;

#define TT_TAILLE 65536
static TTEntree table[TT_TAILLE];

static unsigned long hashCle(const char *s) {
    unsigned long h = 5381;
    int c;
    while ((c = (unsigned char)*s++)) h = ((h << 5) + h) + (unsigned long)c;
    return h;
}

static void tableTranspositionReset(void) {
    memset(table, 0, sizeof(table));
}

static int tableTranspositionGet(const char *cle, double *score, int profondeurMin) {
    unsigned long h = hashCle(cle) % TT_TAILLE;
    TTEntree *e = &table[h];
    if (e->occupee && strcmp(e->cle, cle) == 0 && e->profondeur >= profondeurMin) {
        *score = e->score;
        return 1;
    }
    return 0;
}

static void tableTranspositionSet(const char *cle, double score, int profondeur) {
    unsigned long h = hashCle(cle) % TT_TAILLE;
    TTEntree *e = &table[h];
    strncpy(e->cle, cle, sizeof(e->cle) - 1);
    e->cle[sizeof(e->cle) - 1] = '\0';
    e->score = score;
    e->profondeur = profondeur;
    e->occupee = 1;
}


/* ---------- Tri des coups par nbPrises décroissant (Move Ordering), comme coups.sort(...) en JS ---------- */
static int comparerCoupsNbPrises(const void *a, const void *b) {
    const CoupComplet *ca = a, *cb = b;
    return cb->info.nbPrises - ca->info.nbPrises;
}

static double quiescence(Plateau plat, double alpha, double beta, int estMax);

/* ---------- minimax : équivalent JS minimax ---------- */
static double minimax(Plateau plat, int profondeur, int estMax, double alpha, double beta) {
    char cle[300];
    genererClePlateau(plat, cle, sizeof(cle));

    double cached;
    if (tableTranspositionGet(cle, &cached, profondeur)) {
        return cached;
    }

    if (profondeur <= 0) return quiescence(plat, alpha, beta, estMax);

    int couleurIA = (couleurHumain == BLANC) ? NOIR : BLANC;
    int joueurVirtuel = estMax ? couleurIA : couleurHumain;

    CoupComplet coups[MAX_COUPS_TOTAL];
    int nCoups = getTousLesCoupsPour(joueurVirtuel, plat, coups);

    if (nCoups == 0) return estMax ? (-100000 + profondeur) : (100000 - profondeur);

    qsort(coups, (size_t)nCoups, sizeof(CoupComplet), comparerCoupsNbPrises);

    double evalFinale;

    if (estMax) {
        double maxEval = -INFINITY;
        for (int i = 0; i < nCoups; i++) {
            Plateau platSimule;
            clonerPlateau(plat, platSimule);
            appliquerCoupSimule(coups[i], platSimule);
            int encoreDesPrises = coups[i].info.prise && (coups[i].info.nbPrises > 1);
            double evalCoup = minimax(platSimule, profondeur - 1, encoreDesPrises, alpha, beta);
            if (evalCoup > maxEval) maxEval = evalCoup;
            if (evalCoup > alpha) alpha = evalCoup;
            if (beta <= alpha) break;
        }
        evalFinale = maxEval;
    } else {
        double minEval = INFINITY;
        for (int i = 0; i < nCoups; i++) {
            Plateau platSimule;
            clonerPlateau(plat, platSimule);
            appliquerCoupSimule(coups[i], platSimule);
            int encoreDesPrises = coups[i].info.prise && (coups[i].info.nbPrises > 1);
            double evalCoup = minimax(platSimule, profondeur - 1, !encoreDesPrises, alpha, beta);
            if (evalCoup < minEval) minEval = evalCoup;
            if (evalCoup < beta) beta = evalCoup;
            if (beta <= alpha) break;
        }
        evalFinale = minEval;
    }

    tableTranspositionSet(cle, evalFinale, profondeur);
    return evalFinale;
}

/* ---------- quiescence : équivalent JS quiescence ---------- */
static double quiescence(Plateau plat, double alpha, double beta, int estMax) {
    double scoreValeur = evaluerPlateau(plat);
    if (estMax) {
        if (scoreValeur >= beta) return beta;
        if (scoreValeur > alpha) alpha = scoreValeur;
    } else {
        if (scoreValeur <= alpha) return alpha;
        if (scoreValeur < beta) beta = scoreValeur;
    }

    int couleurIA = (couleurHumain == BLANC) ? NOIR : BLANC;
    int joueurVirtuel = estMax ? couleurIA : couleurHumain;

    CoupComplet tousCoups[MAX_COUPS_TOTAL];
    int nTous = getTousLesCoupsPour(joueurVirtuel, plat, tousCoups);

    for (int i = 0; i < nTous; i++) {
        if (!tousCoups[i].info.prise) continue;
        Plateau platSimule;
        clonerPlateau(plat, platSimule);
        appliquerCoupSimule(tousCoups[i], platSimule);
        double evalCoup = quiescence(platSimule, alpha, beta, !estMax);
        if (estMax) {
            if (evalCoup > alpha) alpha = evalCoup;
            if (alpha >= beta) break;
        } else {
            if (evalCoup < beta) beta = evalCoup;
            if (beta <= alpha) break;
        }
    }
    return estMax ? alpha : beta;
}

/* ---------- trouverMeilleurCoup : équivalent de la boucle du Worker (creerIAWorker.onmessage) ---------- */
static int trouverMeilleurCoup(Plateau plateau, int joueurActuel, int profondeurMax, int couleurHumainParam,
                                CoupComplet *meilleurCoupOut, double *meilleurScoreOut) {
    couleurHumain = couleurHumainParam;
    tableTranspositionReset();

    CoupComplet coups[MAX_COUPS_TOTAL];
    int nCoups = getTousLesCoupsPour(joueurActuel, plateau, coups);
    if (nCoups == 0) return 0;

    qsort(coups, (size_t)nCoups, sizeof(CoupComplet), comparerCoupsNbPrises);

    CoupComplet meilleurCoup = coups[0];
    double meilleurScore = -INFINITY;

    /* Équivalent JS : mode "faible" -> 35% de chance de jouer un coup au hasard
       plutôt que de chercher le meilleur (rend l'IA battable). */
    static int rngInitialise = 0;
    if (!rngInitialise) { srand((unsigned)time(NULL)); rngInitialise = 1; }

    if (profondeurMax == 1 && nCoups > 1 && ((double)rand() / ((double)RAND_MAX + 1.0)) < 0.35) {
        meilleurCoup = coups[rand() % nCoups];
        meilleurScore = 0; /* non calculé dans ce cas, comme en JS */
        *meilleurCoupOut = meilleurCoup;
        *meilleurScoreOut = meilleurScore;
        return 1;
    }

    for (int i = 0; i < nCoups; i++) {
        Plateau platSimule;
        clonerPlateau(plateau, platSimule);
        appliquerCoupSimule(coups[i], platSimule);
        int encoreDesPrises = coups[i].info.prise && (coups[i].info.nbPrises > 1);
        double score = minimax(platSimule, profondeurMax - 1, encoreDesPrises, -INFINITY, INFINITY);
        if (score > meilleurScore) {
            meilleurScore = score;
            meilleurCoup = coups[i];
        }
    }

    *meilleurCoupOut = meilleurCoup;
    *meilleurScoreOut = meilleurScore;
    return 1;
}

/* ---------- Position initiale : équivalent JS placerPions() ---------- */
static void plateauInitial(Plateau plat) {
    for (int x = 0; x < TAILLE; x++)
        for (int z = 0; z < TAILLE; z++)
            plat[x][z] = (Case){ VIDE, 0 };

    for (int z = 0; z < 4; z++)
        for (int x = 0; x < TAILLE; x++)
            if ((x + z) % 2 == 1) plat[x][z] = (Case){ NOIR, 0 };

    for (int z = 6; z < 10; z++)
        for (int x = 0; x < TAILLE; x++)
            if ((x + z) % 2 == 1) plat[x][z] = (Case){ BLANC, 0 };
}

/* ==========================================================
   PONT WEBASSEMBLY — appelé depuis le Web Worker JS
   ==========================================================
   Encodage plat (1 octet par case, tableau de 100) reçu depuis JS :
     -1 = case vide
      0 = pion blanc      1 = dame blanche
      2 = pion noir       3 = dame noire
   Ce mapping est repris à l'identique côté JS (fonction
   encoderPlateau dans le Worker) pour rester synchronisé.
   ========================================================== */
static void depuisFlat(const int8_t *flat, Plateau plat) {
    for (int x = 0; x < TAILLE; x++) {
        for (int z = 0; z < TAILLE; z++) {
            int8_t v = flat[x * TAILLE + z];
            switch (v) {
                case 0:  plat[x][z] = (Case){ BLANC, 0 }; break;
                case 1:  plat[x][z] = (Case){ BLANC, 1 }; break;
                case 2:  plat[x][z] = (Case){ NOIR, 0 };  break;
                case 3:  plat[x][z] = (Case){ NOIR, 1 };  break;
                default: plat[x][z] = (Case){ VIDE, 0 };  break;
            }
        }
    }
}

/* Seul point d'entrée exposé au JS. Une seule requête à la fois (le Worker
   JS ne fait qu'un appel par tour, comme l'ancien code JS). Le résultat est
   renvoyé en JSON dans un buffer statique — suffisant ici car Emscripten
   copie immédiatement la chaîne côté JS (ccall avec returnType 'string')
   avant tout appel suivant. */
EMSCRIPTEN_KEEPALIVE
char *wasm_calculerMeilleurCoup(int8_t *flat, int joueurActuel, int profondeurMax, int couleurHumainParam) {
    static char buffer[160];

    Plateau plateau;
    depuisFlat(flat, plateau);

    CoupComplet meilleurCoup;
    double meilleurScore;
    int ok = trouverMeilleurCoup(plateau, joueurActuel, profondeurMax, couleurHumainParam, &meilleurCoup, &meilleurScore);

    if (!ok) {
        snprintf(buffer, sizeof(buffer), "{\"aucunCoup\":true}");
    } else {
        snprintf(buffer, sizeof(buffer),
                 "{\"x1\":%d,\"z1\":%d,\"x2\":%d,\"z2\":%d,\"prise\":%d,\"px\":%d,\"pz\":%d,\"score\":%g}",
                 meilleurCoup.x1, meilleurCoup.z1, meilleurCoup.x2, meilleurCoup.z2,
                 meilleurCoup.info.prise, meilleurCoup.info.px, meilleurCoup.info.pz,
                 meilleurScore);
    }
    return buffer;
}

#ifndef __EMSCRIPTEN__
/* ---------- main : lance la recherche sur la position initiale, comme le test JS ----------
   Compilé uniquement en natif (tests locaux). Absent du build WebAssembly. */
int main(int argc, char **argv) {
    const char *modeJeu = (argc > 1) ? argv[1] : "normal";
    int profondeurMax;
    if (strcmp(modeJeu, "faible") == 0) profondeurMax = 1;
    else if (strcmp(modeJeu, "moyen") == 0) profondeurMax = 3;
    else if (strcmp(modeJeu, "normal") == 0) profondeurMax = 5;
    else if (strcmp(modeJeu, "expert") == 0) profondeurMax = 7;
    else { fprintf(stderr, "Mode inconnu: %s\n", modeJeu); return 1; }

    Plateau plateau;
    plateauInitial(plateau);

    clock_t t0 = clock();
    CoupComplet meilleurCoup;
    double meilleurScore;
    /* L'IA joue les noirs (couleurHumain = BLANC), les noirs jouent en premier */
    int ok = trouverMeilleurCoup(plateau, NOIR, profondeurMax, BLANC, &meilleurCoup, &meilleurScore);
    clock_t t1 = clock();

    if (!ok) {
        printf("{\"aucunCoup\": true}\n");
        return 0;
    }

    double tempsMs = 1000.0 * (double)(t1 - t0) / CLOCKS_PER_SEC;
    printf("{\"mode\": \"%s\", \"coup\": {\"x1\": %d, \"z1\": %d, \"x2\": %d, \"z2\": %d}, \"score\": %g, \"tempsMs\": %.1f}\n",
           modeJeu, meilleurCoup.x1, meilleurCoup.z1, meilleurCoup.x2, meilleurCoup.z2, meilleurScore, tempsMs);

    tableTranspositionReset();
    return 0;
}
#endif /* __EMSCRIPTEN__ */
