/* ==========================================================
   moteur.c — Portage en C du moteur IA du jeu de Dames
   ==========================================================
   Portage FIDÈLE des fonctions JS suivantes (aucune logique
   modifiée, juste traduite) :
     clonerPlateau, dansPlateau, getCoupsPion, getCoupsDame,
     getTousLesCoups, getTousLesCoupsPour, hash Zobrist,
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
#include <stdint.h>

#ifdef __EMSCRIPTEN__
#include <emscripten/emscripten.h>
#else
#define EMSCRIPTEN_KEEPALIVE
#endif

#define TAILLE 10
#define BLANC 0
#define NOIR 1
#define VIDE (-1)
/* Case occupée par une pièce capturée plus tôt dans la même rafle (séquence
 * de prises) mais pas encore réellement retirée : elle bloque le passage
 * (on ne peut ni la traverser ni la re-capturer), sans être une case vide
 * ni une pièce jouable. Miroir exact de CASE_CAPTUREE côté JS. */
#define BLOQUE 2

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

/*
 * MAKE / UNMAKE
 * -------------
 * Le moteur n'a plus besoin de copier les 100 cases du plateau à chaque
 * branche de l'arbre de recherche. Un coup est appliqué directement sur le
 * plateau courant puis restauré exactement dans son état précédent.
 *
 * On conserve volontairement toutes les informations nécessaires pour que
 * cette optimisation ne modifie ni les règles ni l'évaluation :
 * - case d'origine avant le coup
 * - case de destination avant le coup
 * - case capturée avant le coup
 * - présence éventuelle d'une capture
 *
 * clonerPlateau() reste présent pour conserver une référence simple du
 * comportement historique, mais n'est plus utilisé dans la recherche.
 */
typedef struct {
    int x1, z1, x2, z2;
    int px, pz;
    int hasCapture;
    Case originBefore;
    Case destinationBefore;
    Case capturedBefore;
    uint64_t hashBefore;
} UndoCoup;

/* ---------- Hash Zobrist ----------
 * Une clé 64 bits déterministe par case et type de pièce.
 * Elle remplace la construction d'une chaîne de caractères à chaque nœud.
 * Le générateur est fixe afin que les recherches restent reproductibles.
 */
static uint64_t zobrist[TAILLE][TAILLE][4];
static int zobristInitialise = 0;
/* Deux composantes supplémentaires pour distinguer le joueur à jouer dans
 * la table de transposition. Le même plateau peut apparaître avec un côté
 * différent, notamment à cause des séquences de prises multiples. */
static uint64_t zobristTour[2];

static uint64_t splitmix64(uint64_t *state) {
    uint64_t z = (*state += UINT64_C(0x9E3779B97F4A7C15));
    z = (z ^ (z >> 30)) * UINT64_C(0xBF58476D1CE4E5B9);
    z = (z ^ (z >> 27)) * UINT64_C(0x94D049BB133111EB);
    return z ^ (z >> 31);
}

static inline int indicePiece(Case p) {
    if (p.couleur == BLANC) return p.estDame ? 1 : 0;
    if (p.couleur == NOIR)  return p.estDame ? 3 : 2;
    return -1;
}

static void initialiserZobrist(void) {
    if (zobristInitialise) return;
    uint64_t seed = UINT64_C(0xD4A1E5B7C39F2711);
    for (int x = 0; x < TAILLE; x++) {
        for (int z = 0; z < TAILLE; z++) {
            for (int piece = 0; piece < 4; piece++) {
                zobrist[x][z][piece] = splitmix64(&seed);
            }
        }
    }
    zobristTour[0] = splitmix64(&seed);
    zobristTour[1] = splitmix64(&seed);
    zobristInitialise = 1;
}

static uint64_t calculerHashZobrist(Plateau plat) {
    uint64_t hash = 0;
    for (int x = 0; x < TAILLE; x++) {
        for (int z = 0; z < TAILLE; z++) {
            int piece = indicePiece(plat[x][z]);
            if (piece >= 0) hash ^= zobrist[x][z][piece];
        }
    }
    return hash;
}

static inline uint64_t hashAvecPiece(uint64_t hash, int x, int z, Case p) {
    int piece = indicePiece(p);
    return piece >= 0 ? (hash ^ zobrist[x][z][piece]) : hash;
}

static inline void makeMove(const CoupComplet *coup, Plateau plat, uint64_t *hash, UndoCoup *undo) {
    undo->x1 = coup->x1;
    undo->z1 = coup->z1;
    undo->x2 = coup->x2;
    undo->z2 = coup->z2;
    undo->px = coup->info.px;
    undo->pz = coup->info.pz;
    undo->hasCapture = coup->info.prise ? 1 : 0;
    undo->originBefore = plat[coup->x1][coup->z1];
    undo->destinationBefore = plat[coup->x2][coup->z2];
    undo->capturedBefore = undo->hasCapture
        ? plat[coup->info.px][coup->info.pz]
        : (Case){ VIDE, 0 };
    undo->hashBefore = *hash;

    Case pionOrigine = undo->originBefore;
    if (pionOrigine.couleur == VIDE) return;

    /* Retirer du hash les anciennes pièces affectées par le coup. */
    *hash = hashAvecPiece(*hash, coup->x1, coup->z1, undo->originBefore);
    *hash = hashAvecPiece(*hash, coup->x2, coup->z2, undo->destinationBefore);
    if (undo->hasCapture) {
        *hash = hashAvecPiece(*hash, coup->info.px, coup->info.pz, undo->capturedBefore);
    }

    plat[coup->x1][coup->z1] = (Case){ VIDE, 0 };
    if (undo->hasCapture) {
        /* La pièce capturée reste "présente" (bloquante) tant que la rafle
         * n'est pas terminée — voir CASE_CAPTUREE côté JS. unmakeMove()
         * restaure de toute façon la vraie pièce via capturedBefore, donc
         * ce marqueur ne fuit jamais en dehors de la branche de recherche
         * en cours. */
        plat[coup->info.px][coup->info.pz] = (Case){ BLOQUE, 0 };
    }

    plat[coup->x2][coup->z2] = pionOrigine;

    /* Promotion identique à appliquerCoupSimule(). */
    if (plat[coup->x2][coup->z2].couleur == BLANC && coup->z2 == 0)
        plat[coup->x2][coup->z2].estDame = 1;
    if (plat[coup->x2][coup->z2].couleur == NOIR && coup->z2 == 9)
        plat[coup->x2][coup->z2].estDame = 1;

    /* Ajouter la pièce finale (pion ou dame après promotion). */
    *hash = hashAvecPiece(*hash, coup->x2, coup->z2, plat[coup->x2][coup->z2]);
}

static inline void unmakeMove(Plateau plat, uint64_t *hash, const UndoCoup *undo) {
    plat[undo->x1][undo->z1] = undo->originBefore;
    plat[undo->x2][undo->z2] = undo->destinationBefore;
    if (undo->hasCapture) {
        plat[undo->px][undo->pz] = undo->capturedBefore;
    }
    *hash = undo->hashBefore;
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
                plat[nx][nz].couleur != BLOQUE &&
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
            } else if (plat[nx][nz].couleur == BLOQUE) {
                /* Pièce déjà capturée plus tôt dans la même rafle : bloque
                 * encore le passage, ni traversable ni re-capturable. */
                break;
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
static int getTousLesCoups(int x, int z, Plateau plat, Coup out[MAX_COUPS], uint64_t *hash) {
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
        /* Même recherche qu'avant, mais sans copier le plateau. */
        CoupComplet tempCoup = {
            .x1 = x, .z1 = z, .x2 = c.x, .z2 = c.z, .info = c
        };
        UndoCoup undo;
        makeMove(&tempCoup, plat, hash, &undo);

        Coup chaines[MAX_COUPS];
        int nChaines = getTousLesCoups(c.x, c.z, plat, chaines, hash);
        unmakeMove(plat, hash, &undo);
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
static int getTousLesCoupsPour(int couleur, Plateau plat, CoupComplet out[MAX_COUPS_TOTAL], uint64_t *hash) {
    CoupComplet tous[MAX_COUPS_TOTAL];
    int nTous = 0;
    int aUnePrise = 0;

    for (int x = 0; x < TAILLE; x++) {
        for (int z = 0; z < TAILLE; z++) {
            Case pion = plat[x][z];
            if (pion.couleur == couleur) {
                Coup coups[MAX_COUPS];
                int nc = getTousLesCoups(x, z, plat, coups, hash);
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

/* ---------- evaluerPlateau : équivalent JS evaluerPlateau ---------- */
static double evaluerPlateau(Plateau plat) {
    int couleurIA = (couleurHumain == BLANC) ? NOIR : BLANC;
    double score = 0;
    int totalPions = 0;

    for (int x = 0; x < TAILLE; x++)
        for (int z = 0; z < TAILLE; z++)
            if (plat[x][z].couleur != VIDE && plat[x][z].couleur != BLOQUE) totalPions++;

    int estFinDePartie = totalPions <= 7;

    for (int x = 0; x < TAILLE; x++) {
        for (int z = 0; z < TAILLE; z++) {
            Case p = plat[x][z];
            if (p.couleur == VIDE || p.couleur == BLOQUE) continue;

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


/* ---------- Table de transposition ----------
 * Étape 3 : bornes Alpha-Beta + meilleur coup.
 *
 * Une entrée peut représenter :
 *   TT_EXACT       : score exact de la position à cette profondeur
 *   TT_LOWER_BOUND : score >= valeur mémorisée (fail-high)
 *   TT_UPPER_BOUND : score <= valeur mémorisée (fail-low)
 *
 * Le meilleur coup mémorisé sert uniquement à l'ordre de recherche : il est
 * placé en tête lorsqu'il est encore légal dans la liste de coups courante.
 * Cela ne change pas les règles ni la profondeur de recherche.
 */
typedef enum {
    TT_EXACT = 1,
    TT_LOWER_BOUND = 2,
    TT_UPPER_BOUND = 3
} TTType;

typedef struct {
    uint64_t cle;
    double score;
    int profondeur;
    uint8_t type;
    uint8_t occupee;
    CoupComplet meilleurCoup;
} TTEntree;

#define TT_TAILLE 65536
static TTEntree table[TT_TAILLE];

static inline uint32_t indexTT(uint64_t cle) {
    uint64_t h = cle ^ (cle >> 32);
    h ^= h >> 16;
    return (uint32_t)h & (TT_TAILLE - 1);
}

static void tableTranspositionReset(void) {
    memset(table, 0, sizeof(table));
}

static inline int coupsIdentiques(const CoupComplet *a, const CoupComplet *b) {
    return a->x1 == b->x1 && a->z1 == b->z1 &&
           a->x2 == b->x2 && a->z2 == b->z2 &&
           a->info.prise == b->info.prise &&
           a->info.px == b->info.px && a->info.pz == b->info.pz;
}

/*
 * Recherche TT :
 * - permet toujours de récupérer le meilleur coup pour l'ordre de recherche ;
 * - n'utilise le score que si la profondeur demandée est couverte et que la
 *   borne permet réellement une coupure ou donne un résultat exact.
 */
static int tableTranspositionProbe(uint64_t cle, int profondeur,
                                   double alpha, double beta,
                                   double *score, CoupComplet *meilleurCoup,
                                   int *aMeilleurCoup) {
    TTEntree *e = &table[indexTT(cle)];
    if (!e->occupee || e->cle != cle) return 0;

    if (meilleurCoup && aMeilleurCoup) {
        *aMeilleurCoup = 0;
        if (e->meilleurCoup.x1 >= 0) {
            *meilleurCoup = e->meilleurCoup;
            *aMeilleurCoup = 1;
        }
    }

    if (e->profondeur < profondeur) return 0;

    if (e->type == TT_EXACT) {
        if (score) *score = e->score;
        return 1;
    }
    if (e->type == TT_LOWER_BOUND && e->score >= beta) {
        if (score) *score = e->score;
        return 1;
    }
    if (e->type == TT_UPPER_BOUND && e->score <= alpha) {
        if (score) *score = e->score;
        return 1;
    }
    return 0;
}

static void tableTranspositionSet(uint64_t cle, double score, int profondeur,
                                  TTType type, const CoupComplet *meilleurCoup) {
    TTEntree *e = &table[indexTT(cle)];

    /* Remplacer une entrée seulement si elle est vide ou si la nouvelle
       recherche est au moins aussi profonde. On conserve ainsi les résultats
       plus utiles lorsqu'il y a collision. */
    if (e->occupee && e->cle == cle && e->profondeur > profondeur) return;

    e->cle = cle;
    e->score = score;
    e->profondeur = profondeur;
    e->type = (uint8_t)type;
    e->occupee = 1;
    if (meilleurCoup) {
        e->meilleurCoup = *meilleurCoup;
    } else {
        e->meilleurCoup = (CoupComplet){ .x1 = -1, .z1 = -1, .x2 = -1, .z2 = -1 };
    }
}

/* ---------- Move ordering avancé ----------
 *
 * Ordre de priorité :
 *   1. meilleur coup de la TT
 *   2. nombre de prises (règle existante, priorité absolue)
 *   3. killer moves (coups calmes ayant déjà provoqué une coupure)
 *   4. history heuristic (coups calmes souvent utiles)
 *
 * Cette heuristique ne retire aucun coup et ne change aucune profondeur.
 * Elle cherche simplement à présenter plus tôt les coups susceptibles de
 * provoquer une coupure Alpha-Beta.
 */
#define MAX_PROFONDEUR_RECHERCHE 16
#define HIST_X 10
#define HIST_Z 10
#define HIST_TAILLE (HIST_X * HIST_Z * HIST_X * HIST_Z)

static unsigned int historiqueCoups[2][HIST_TAILLE];
static CoupComplet killerCoups[MAX_PROFONDEUR_RECHERCHE + 1][2];
static unsigned char killerValide[MAX_PROFONDEUR_RECHERCHE + 1][2];

static inline int indexHistorique(const CoupComplet *c) {
    return (((c->x1 * 10 + c->z1) * 10 + c->x2) * 10 + c->z2);
}

static inline int estCoupCalme(const CoupComplet *c) {
    return !c->info.prise;
}

static void resetMoveOrdering(void) {
    memset(historiqueCoups, 0, sizeof(historiqueCoups));
    memset(killerValide, 0, sizeof(killerValide));
}

static inline int estKiller(const CoupComplet *c, int profondeur, int slot) {
    return profondeur >= 0 && profondeur <= MAX_PROFONDEUR_RECHERCHE &&
           killerValide[profondeur][slot] &&
           coupsIdentiques(c, &killerCoups[profondeur][slot]);
}

static inline void enregistrerCoupKiller(const CoupComplet *c, int profondeur) {
    if (!estCoupCalme(c) || profondeur < 0 || profondeur > MAX_PROFONDEUR_RECHERCHE) return;
    if (killerValide[profondeur][0] && coupsIdentiques(c, &killerCoups[profondeur][0])) return;

    killerCoups[profondeur][1] = killerCoups[profondeur][0];
    killerValide[profondeur][1] = killerValide[profondeur][0];
    killerCoups[profondeur][0] = *c;
    killerValide[profondeur][0] = 1;
}

static inline void enregistrerHistorique(const CoupComplet *c, int estMax, int profondeur) {
    if (!estCoupCalme(c)) return;
    int idx = indexHistorique(c);
    int side = estMax ? 1 : 0;
    unsigned int bonus = (unsigned int)(profondeur + 1) * (unsigned int)(profondeur + 1);
    unsigned int *h = &historiqueCoups[side][idx];
    /* Saturation douce : évite tout débordement et garde les coups récents
       compétitifs face aux anciens scores. */
    if (*h > 1000000U - bonus) *h = 1000000U;
    else *h += bonus;
}

static inline long long scoreOrdreCoup(const CoupComplet *c,
                                       const CoupComplet *ttCoup, int aTT,
                                       int estMax, int profondeur) {
    /* Les captures maximales doivent rester devant les coups avec moins de
       prises. Le poids est volontairement très supérieur aux heuristiques. */
    long long score = (long long)c->info.nbPrises * 1000000000LL;

    if (aTT && coupsIdentiques(c, ttCoup)) score += 900000000LL;
    if (estKiller(c, profondeur, 0)) score += 200000000LL;
    else if (estKiller(c, profondeur, 1)) score += 150000000LL;

    if (estCoupCalme(c)) {
        score += (long long)historiqueCoups[estMax ? 1 : 0][indexHistorique(c)];
    }
    return score;
}

static void ordonnerCoups(CoupComplet *coups, int nCoups,
                          const CoupComplet *ttCoup, int aTT,
                          int estMax, int profondeur) {
    /* Insertion sort : MAX_COUPS_TOTAL reste petit et l'algorithme évite les
       appels indirects de qsort() dans chaque nœud de recherche. */
    for (int i = 1; i < nCoups; i++) {
        CoupComplet courant = coups[i];
        long long scoreCourant = scoreOrdreCoup(&courant, ttCoup, aTT, estMax, profondeur);
        int j = i - 1;
        while (j >= 0) {
            long long scoreAvant = scoreOrdreCoup(&coups[j], ttCoup, aTT, estMax, profondeur);
            if (scoreAvant >= scoreCourant) break;
            coups[j + 1] = coups[j];
            j--;
        }
        coups[j + 1] = courant;
    }
}

/* ---------- Tri racine : on conserve l'ordre historique nbPrises ---------- */
static int comparerCoupsNbPrises(const void *a, const void *b) {
    const CoupComplet *ca = a, *cb = b;
    return cb->info.nbPrises - ca->info.nbPrises;
}

static inline uint64_t cleTableTransposition(uint64_t hash, int estMax) {
    return hash ^ zobristTour[estMax ? 1 : 0];
}

static double quiescence(Plateau plat, uint64_t hash, double alpha, double beta, int estMax);

/* ---------- minimax : équivalent JS minimax ---------- */
static double minimax(Plateau plat, uint64_t hash, int profondeur, int estMax, double alpha, double beta) {
    const double alphaInitial = alpha;
    const double betaInitial = beta;

    double cached;
    CoupComplet ttCoup = { .x1 = -1, .z1 = -1, .x2 = -1, .z2 = -1 };
    int aTTCoup = 0;
    uint64_t cleTT = cleTableTransposition(hash, estMax);
    if (tableTranspositionProbe(cleTT, profondeur, alpha, beta,
                                &cached, &ttCoup, &aTTCoup)) {
        return cached;
    }

    if (profondeur <= 0) return quiescence(plat, hash, alpha, beta, estMax);

    int couleurIA = (couleurHumain == BLANC) ? NOIR : BLANC;
    int joueurVirtuel = estMax ? couleurIA : couleurHumain;

    CoupComplet coups[MAX_COUPS_TOTAL];
    int nCoups = getTousLesCoupsPour(joueurVirtuel, plat, coups, &hash);

    if (nCoups == 0) {
        double terminal = estMax ? (-100000 + profondeur) : (100000 - profondeur);
        tableTranspositionSet(cleTT, terminal, profondeur, TT_EXACT, NULL);
        return terminal;
    }

    ordonnerCoups(coups, nCoups, &ttCoup, aTTCoup, estMax, profondeur);

    double evalFinale;
    CoupComplet meilleurCoupLocal = coups[0];

    if (estMax) {
        double maxEval = -INFINITY;
        for (int i = 0; i < nCoups; i++) {
            UndoCoup undo;
            makeMove(&coups[i], plat, &hash, &undo);
            int encoreDesPrises = coups[i].info.prise && (coups[i].info.nbPrises > 1);
            double evalCoup = minimax(plat, hash, profondeur - 1, encoreDesPrises, alpha, beta);
            unmakeMove(plat, &hash, &undo);

            if (evalCoup > maxEval) {
                maxEval = evalCoup;
                meilleurCoupLocal = coups[i];
            }
            if (evalCoup > alpha) alpha = evalCoup;
            if (beta <= alpha) {
                enregistrerCoupKiller(&coups[i], profondeur);
                enregistrerHistorique(&coups[i], estMax, profondeur);
                break;
            }
        }
        evalFinale = maxEval;
    } else {
        double minEval = INFINITY;
        for (int i = 0; i < nCoups; i++) {
            UndoCoup undo;
            makeMove(&coups[i], plat, &hash, &undo);
            int encoreDesPrises = coups[i].info.prise && (coups[i].info.nbPrises > 1);
            double evalCoup = minimax(plat, hash, profondeur - 1, !encoreDesPrises, alpha, beta);
            unmakeMove(plat, &hash, &undo);

            if (evalCoup < minEval) {
                minEval = evalCoup;
                meilleurCoupLocal = coups[i];
            }
            if (evalCoup < beta) beta = evalCoup;
            if (beta <= alpha) {
                enregistrerCoupKiller(&coups[i], profondeur);
                enregistrerHistorique(&coups[i], estMax, profondeur);
                break;
            }
        }
        evalFinale = minEval;
    }

    TTType type;
    if (evalFinale <= alphaInitial) {
        type = TT_UPPER_BOUND;
    } else if (evalFinale >= betaInitial) {
        type = TT_LOWER_BOUND;
    } else {
        type = TT_EXACT;
    }

    /* hash a été restauré par le dernier unmakeMove : c'est donc bien la clé
       de la position courante, contrairement à l'ancienne version où la TT
       pouvait être écrite avec une clé restaurée d'un contexte différent. */
    tableTranspositionSet(cleTT, evalFinale, profondeur, type, &meilleurCoupLocal);
    return evalFinale;
}

/* ---------- quiescence : équivalent JS quiescence ---------- */
static double quiescence(Plateau plat, uint64_t hash, double alpha, double beta, int estMax) {
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
    int nTous = getTousLesCoupsPour(joueurVirtuel, plat, tousCoups, &hash);

    for (int i = 0; i < nTous; i++) {
        if (!tousCoups[i].info.prise) continue;
        UndoCoup undo;
        makeMove(&tousCoups[i], plat, &hash, &undo);
        double evalCoup = quiescence(plat, hash, alpha, beta, !estMax);
        unmakeMove(plat, &hash, &undo);
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
    initialiserZobrist();
    tableTranspositionReset();
    resetMoveOrdering();

    uint64_t hash = calculerHashZobrist(plateau);

    CoupComplet coups[MAX_COUPS_TOTAL];
    int nCoups = getTousLesCoupsPour(joueurActuel, plateau, coups, &hash);
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
        UndoCoup undo;
        makeMove(&coups[i], plateau, &hash, &undo);
        int encoreDesPrises = coups[i].info.prise && (coups[i].info.nbPrises > 1);
        double score = minimax(plateau, hash, profondeurMax - 1, encoreDesPrises, -INFINITY, INFINITY);
        unmakeMove(plateau, &hash, &undo);
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
                case 4:  plat[x][z] = (Case){ BLOQUE, 0 }; break;
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
