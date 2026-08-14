/* ==========================================================
   moteur.c — moteur IA C/WebAssembly optimisé
   ========================================================== */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
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
#define MAX_COUPS 64
#define MAX_COUPS_TOTAL 512

/* La quiescence n'est PAS volontairement tronquée à quelques coups :
   elle continue tant qu'il existe des prises. Cette borne très haute est
   uniquement un garde-fou contre une corruption/position pathologique. */
#define MAX_Q_DEPTH 32

typedef struct { int8_t couleur; int8_t estDame; } Case;
typedef Case Plateau[TAILLE][TAILLE];

typedef struct {
    int x, z;
    int prise;
    int px, pz;
    int nbPrises;
} Coup;

typedef struct {
    int x1, z1, x2, z2;
    Coup info;
} CoupComplet;

typedef struct {
    int x1, z1, x2, z2;
    int prise, px, pz;
    Case pieceAvant;
    Case pieceDestinationAvant;
    Case piecePriseAvant;
    int avaitPrise;
} UndoCoup;

static const double MATRICE_TACTIQUE[TAILLE][TAILLE] = {
    {1.4,1.2,1.2,1.2,1.2,1.2,1.2,1.2,1.2,1.4},
    {1.1,1.3,1.1,1.1,1.1,1.1,1.1,1.1,1.3,1.1},
    {1.1,1.1,1.3,1.2,1.2,1.2,1.2,1.3,1.1,1.1},
    {1.1,1.1,1.2,1.5,1.4,1.4,1.5,1.2,1.1,1.1},
    {1.1,1.1,1.2,1.4,1.6,1.6,1.4,1.2,1.1,1.1},
    {1.1,1.1,1.2,1.4,1.6,1.6,1.4,1.2,1.1,1.1},
    {1.1,1.1,1.2,1.5,1.4,1.4,1.5,1.2,1.1,1.1},
    {1.1,1.1,1.3,1.2,1.2,1.2,1.2,1.3,1.1,1.1},
    {1.1,1.3,1.1,1.1,1.1,1.1,1.1,1.1,1.3,1.1},
    {1.4,1.2,1.2,1.2,1.2,1.2,1.2,1.2,1.2,1.4}
};

static int couleurHumain = BLANC;
static uint64_t nodesRecherche = 0;
static uint64_t ttHits = 0;
static int qDepthCourante = 0;

/* ---------- Zobrist : évite la génération de chaînes de 100+ caractères ---------- */
static uint64_t zobrist[TAILLE][TAILLE][4];
static uint64_t zobristTour[2];
static int zobristPret = 0;

static uint64_t splitmix64(uint64_t *state) {
    uint64_t z = (*state += UINT64_C(0x9E3779B97F4A7C15));
    z = (z ^ (z >> 30)) * UINT64_C(0xBF58476D1CE4E5B9);
    z = (z ^ (z >> 27)) * UINT64_C(0x94D049BB133111EB);
    return z ^ (z >> 31);
}

static void initZobrist(void) {
    if (zobristPret) return;
    uint64_t seed = UINT64_C(0xD4A35E91C72B6F11);
    for (int x=0;x<TAILLE;x++) for (int z=0;z<TAILLE;z++)
        for (int p=0;p<4;p++) zobrist[x][z][p] = splitmix64(&seed);
    zobristTour[0] = splitmix64(&seed);
    zobristTour[1] = splitmix64(&seed);
    zobristPret = 1;
}

static int pieceIndex(Case p) {
    if (p.couleur == VIDE) return -1;
    return p.couleur * 2 + (p.estDame ? 1 : 0);
}

static uint64_t hashPlateau(Plateau p, int joueur, int estMax) {
    uint64_t h = zobristTour[joueur ^ (estMax ? 0 : 1)];
    for (int x=0;x<TAILLE;x++) for (int z=0;z<TAILLE;z++) {
        int i = pieceIndex(p[x][z]);
        if (i >= 0) h ^= zobrist[x][z][i];
    }
    return h;
}

/* ---------- Table de transposition compacte, sans malloc/free par entrée ---------- */
#define TT_BITS 16
#define TT_TAILLE (1u << TT_BITS)
#define TT_MASK (TT_TAILLE - 1u)
#define TT_EXACT 0
#define TT_LOWER 1
#define TT_UPPER 2

typedef struct {
    uint64_t key;
    double score;
    int16_t profondeur;
    uint8_t flag;
    uint8_t utilise;
} TTEntree;

static TTEntree table[TT_TAILLE];

static void tableTranspositionReset(void) {
    memset(table, 0, sizeof(table));
    ttHits = 0;
}

static int tableTranspositionGet(uint64_t key, int profondeur, double alpha, double beta, double *score) {
    TTEntree *e = &table[(uint32_t)key & TT_MASK];
    if (!e->utilise || e->key != key || e->profondeur < profondeur) return 0;
    ttHits++;
    if (e->flag == TT_EXACT) { *score = e->score; return 1; }
    if (e->flag == TT_LOWER && e->score >= beta) { *score = e->score; return 1; }
    if (e->flag == TT_UPPER && e->score <= alpha) { *score = e->score; return 1; }
    return 0;
}

static void tableTranspositionSet(uint64_t key, double score, int profondeur, uint8_t flag) {
    TTEntree *e = &table[(uint32_t)key & TT_MASK];
    if (!e->utilise || profondeur >= e->profondeur) {
        e->key = key; e->score = score; e->profondeur = (int16_t)profondeur;
        e->flag = flag; e->utilise = 1;
    }
}

static int dansPlateau(int x,int z) { return x>=0 && x<TAILLE && z>=0 && z<TAILLE; }

/* ---------- Génération des coups ---------- */
static int getCoupsPion(int x,int z,Plateau plat,Coup out[MAX_COUPS]) {
    int n=0; Case pion=plat[x][z]; if(pion.couleur==VIDE) return 0;
    int dir=(pion.couleur==BLANC)?-1:1; const int dxs[2]={-1,1};
    for(int i=0;i<2;i++) { int nx=x+dxs[i], nz=z+dir;
        if(dansPlateau(nx,nz) && plat[nx][nz].couleur==VIDE && n<MAX_COUPS)
            out[n++]=(Coup){nx,nz,0,0,0,0}; }
    for(int i=0;i<2;i++) for(int j=0;j<2;j++) {
        int dx=dxs[i], dz=dxs[j], nx=x+dx,nz=z+dz,nx2=x+2*dx,nz2=z+2*dz;
        if(dansPlateau(nx2,nz2) && plat[nx2][nz2].couleur==VIDE &&
           dansPlateau(nx,nz) && plat[nx][nz].couleur!=VIDE && plat[nx][nz].couleur!=pion.couleur && n<MAX_COUPS)
            out[n++]=(Coup){nx2,nz2,1,nx,nz,1};
    }
    return n;
}

static int getCoupsDame(int x,int z,Plateau plat,Coup out[MAX_COUPS]) {
    int n=0; Case pion=plat[x][z]; const int dirs[4][2]={{1,1},{1,-1},{-1,1},{-1,-1}};
    for(int d=0;d<4;d++) { int dx=dirs[d][0],dz=dirs[d][1],nx=x+dx,nz=z+dz;
        int rencontre=0,prx=0,prz=0;
        while(dansPlateau(nx,nz)) {
            if(plat[nx][nz].couleur==VIDE) {
                if(n<MAX_COUPS) out[n++]=(Coup){nx,nz,rencontre,prx,prz,rencontre?1:0};
            } else if(plat[nx][nz].couleur==pion.couleur) break;
            else { if(rencontre) break; rencontre=1; prx=nx; prz=nz; }
            nx+=dx; nz+=dz;
        }
    }
    return n;
}

/* Applique/restaure un coup sans cloner le plateau. */
static void appliquerCoupUndo(CoupComplet c, Plateau p, UndoCoup *u) {
    u->x1=c.x1;u->z1=c.z1;u->x2=c.x2;u->z2=c.z2;
    u->prise=c.info.prise;u->px=c.info.px;u->pz=c.info.pz;u->avaitPrise=c.info.prise;
    u->pieceAvant=p[c.x1][c.z1];
    u->pieceDestinationAvant=p[c.x2][c.z2];
    u->piecePriseAvant=c.info.prise ? p[c.info.px][c.info.pz] : (Case){VIDE,0};
    Case piece=u->pieceAvant;
    p[c.x1][c.z1]=(Case){VIDE,0};
    p[c.x2][c.z2]=piece;
    if(c.info.prise) p[c.info.px][c.info.pz]=(Case){VIDE,0};
    if(p[c.x2][c.z2].couleur==BLANC && c.z2==0) p[c.x2][c.z2].estDame=1;
    if(p[c.x2][c.z2].couleur==NOIR && c.z2==9) p[c.x2][c.z2].estDame=1;
}

static void annulerCoupUndo(const UndoCoup *u, Plateau p) {
    p[u->x1][u->z1]=u->pieceAvant;
    p[u->x2][u->z2]=u->pieceDestinationAvant;
    if(u->avaitPrise) p[u->px][u->pz]=u->piecePriseAvant;
}

/* Calcule uniquement le nombre maximal de prises supplémentaires. Aucun clone. */
static int profondeurRafle(int x,int z,Plateau plat) {
    Case pion=plat[x][z];
    Coup bruts[MAX_COUPS];
    int n=pion.estDame?getCoupsDame(x,z,plat,bruts):getCoupsPion(x,z,plat,bruts);
    int max=0;
    for(int i=0;i<n;i++) if(bruts[i].prise) {
        CoupComplet cc={x,z,bruts[i].x,bruts[i].z,bruts[i]};
        UndoCoup u; appliquerCoupUndo(cc,plat,&u);
        int suite=1+profondeurRafle(bruts[i].x,bruts[i].z,plat);
        annulerCoupUndo(&u,plat);
        if(suite>max) max=suite;
    }
    return max;
}

static int getTousLesCoups(int x,int z,Plateau plat,Coup out[MAX_COUPS]) {
    Case pion=plat[x][z]; if(pion.couleur==VIDE) return 0;
    Coup bruts[MAX_COUPS];
    int nb=pion.estDame?getCoupsDame(x,z,plat,bruts):getCoupsPion(x,z,plat,bruts);
    int n=0;
    for(int i=0;i<nb && n<MAX_COUPS;i++) {
        Coup c=bruts[i];
        if (c.prise) {
            CoupComplet cc={x,z,c.x,c.z,c};
            UndoCoup u;
            appliquerCoupUndo(cc,plat,&u);
            c.nbPrises=1+profondeurRafle(c.x,c.z,plat);
            annulerCoupUndo(&u,plat);
        } else {
            c.nbPrises=0;
        }
        out[n++]=c;
    }
    return n;
}

static int getTousLesCoupsPour(int couleur,Plateau plat,CoupComplet out[MAX_COUPS_TOTAL]) {
    int n=0,aUnePrise=0;
    for(int x=0;x<TAILLE;x++) for(int z=0;z<TAILLE;z++) {
        if(plat[x][z].couleur!=couleur) continue;
        Coup coups[MAX_COUPS]; int nc=getTousLesCoups(x,z,plat,coups);
        for(int i=0;i<nc;i++) {
            if(coups[i].prise) aUnePrise=1;
            if(n<MAX_COUPS_TOTAL) out[n++]=(CoupComplet){x,z,coups[i].x,coups[i].z,coups[i]};
        }
    }
    if(!aUnePrise) return n;
    int w=0; for(int i=0;i<n;i++) if(out[i].info.prise) out[w++]=out[i];
    return w;
}

static double evaluerPlateau(Plateau plat) {
    int couleurIA=(couleurHumain==BLANC)?NOIR:BLANC; double score=0; int total=0;
    for(int x=0;x<TAILLE;x++) for(int z=0;z<TAILLE;z++) if(plat[x][z].couleur!=VIDE) total++;
    int fin=total<=7;
    for(int x=0;x<TAILLE;x++) for(int z=0;z<TAILLE;z++) {
        Case p=plat[x][z]; if(p.couleur==VIDE) continue; double v;
        if(p.estDame) { v=fin?3800:3200; double dc=fabs(x-4.5)+fabs(z-4.5); v+=(9-dc)*20; }
        else { v=1000; v+=MATRICE_TACTIQUE[x][z]*100; v+=(p.couleur==NOIR?z:9-z)*40; }
        if(x==0||x==9) v+=45;
        if(!fin) { if(p.couleur==NOIR&&z==0)v+=90; if(p.couleur==BLANC&&z==9)v+=90; }
        int dir=p.couleur==NOIR?-1:1;
        if(dansPlateau(x-1,z+dir)&&plat[x-1][z+dir].couleur==p.couleur)v+=25;
        if(dansPlateau(x+1,z+dir)&&plat[x+1][z+dir].couleur==p.couleur)v+=25;
        score+=(p.couleur==couleurIA)?v:-v;
    }
    return score;
}

static int comparerCoupsNbPrises(const void*a,const void*b) {
    const CoupComplet*ca=(const CoupComplet*)a,*cb=(const CoupComplet*)b;
    return cb->info.nbPrises-ca->info.nbPrises;
}

static double quiescence(Plateau plat,double alpha,double beta,int estMax,int profondeurQ);

static double minimax(Plateau plat,int profondeur,int estMax,double alpha,double beta,uint64_t hash,int joueur) {
    nodesRecherche++;
    double cached;
    if(tableTranspositionGet(hash,profondeur,alpha,beta,&cached)) return cached;
    if(profondeur<=0) return quiescence(plat,alpha,beta,estMax,0);

    int couleurIA=(couleurHumain==BLANC)?NOIR:BLANC;
    int joueurVirtuel=estMax?couleurIA:couleurHumain;
    CoupComplet coups[MAX_COUPS_TOTAL];
    int n=getTousLesCoupsPour(joueurVirtuel,plat,coups);
    if(n==0) return estMax?-100000.0+profondeur:100000.0-profondeur;
    qsort(coups,(size_t)n,sizeof(CoupComplet),comparerCoupsNbPrises);

    double alphaOrig=alpha,betaOrig=beta,evalFinale;
    if(estMax) {
        double best=-INFINITY;
        for(int i=0;i<n;i++) { UndoCoup u; appliquerCoupUndo(coups[i],plat,&u);
            int prochain=coups[i].info.prise && coups[i].info.nbPrises>1 ? estMax : 0;
            /* Le plateau est minuscule : recalculer le hash évite toute erreur
               de hash incrémental autour de la promotion/prise et reste bien
               moins cher que la génération de chaîne JS. */
            uint64_t h2=hashPlateau(plat,joueurVirtuel^1,prochain);
            double s=minimax(plat,profondeur-1,prochain,alpha,beta,h2,joueurVirtuel^1);
            annulerCoupUndo(&u,plat);
            if(s>best)best=s; if(s>alpha)alpha=s; if(beta<=alpha)break;
        }
        evalFinale=best;
    } else {
        double best=INFINITY;
        for(int i=0;i<n;i++) { UndoCoup u; appliquerCoupUndo(coups[i],plat,&u);
            int prochain=coups[i].info.prise && coups[i].info.nbPrises>1 ? 0 : 1;
            uint64_t h2=hashPlateau(plat,joueurVirtuel^1,prochain);
            double s=minimax(plat,profondeur-1,prochain,alpha,beta,h2,joueurVirtuel^1);
            annulerCoupUndo(&u,plat);
            if(s<best)best=s; if(s<beta)beta=s; if(beta<=alpha)break;
        }
        evalFinale=best;
    }
    uint8_t flag=(evalFinale<=alphaOrig)?TT_UPPER:((evalFinale>=betaOrig)?TT_LOWER:TT_EXACT);
    tableTranspositionSet(hash,evalFinale,profondeur,flag);
    return evalFinale;
}

/* Quiescence contrôlée intelligemment :
   - aucune coupure artificielle à 2/4 niveaux ;
   - on explore toutes les prises disponibles avec alpha-beta ;
   - MAX_Q_DEPTH=32 est seulement un filet de sécurité extrême ;
   - le même make/unmake évite les copies de plateaux ;
   - l'évaluation n'est arrêtée que lorsqu'il n'y a plus de prise ou que
     le garde-fou pathologique est atteint. */
static double quiescence(Plateau plat,double alpha,double beta,int estMax,int profondeurQ) {
    nodesRecherche++;
    double score=evaluerPlateau(plat);
    if(estMax) { if(score>=beta)return beta; if(score>alpha)alpha=score; }
    else { if(score<=alpha)return alpha; if(score<beta)beta=score; }
    if(profondeurQ>=MAX_Q_DEPTH) return estMax?alpha:beta;

    int couleurIA=(couleurHumain==BLANC)?NOIR:BLANC;
    int joueurVirtuel=estMax?couleurIA:couleurHumain;
    CoupComplet coups[MAX_COUPS_TOTAL];
    int n=getTousLesCoupsPour(joueurVirtuel,plat,coups);
    qsort(coups,(size_t)n,sizeof(CoupComplet),comparerCoupsNbPrises);
    int aPrise=0; for(int i=0;i<n;i++) if(coups[i].info.prise){aPrise=1;break;}
    if(!aPrise) return estMax?alpha:beta;

    for(int i=0;i<n;i++) if(coups[i].info.prise) {
        UndoCoup u; appliquerCoupUndo(coups[i],plat,&u);
        double s=quiescence(plat,alpha,beta,!estMax,profondeurQ+1);
        annulerCoupUndo(&u,plat);
        if(estMax){if(s>alpha)alpha=s;if(alpha>=beta)break;}
        else {if(s<beta)beta=s;if(beta<=alpha)break;}
    }
    return estMax?alpha:beta;
}

static int trouverMeilleurCoup(Plateau plateau,int joueurActuel,int profondeurMax,int couleurHumainParam,CoupComplet*out,double*scoreOut) {
    initZobrist(); couleurHumain=couleurHumainParam; nodesRecherche=0; tableTranspositionReset();
    CoupComplet coups[MAX_COUPS_TOTAL]; int n=getTousLesCoupsPour(joueurActuel,plateau,coups); if(n==0)return 0;
    qsort(coups,(size_t)n,sizeof(CoupComplet),comparerCoupsNbPrises);
    CoupComplet best=coups[0]; double bestScore=-INFINITY;
    static int rng=0; if(!rng){srand((unsigned)time(NULL));rng=1;}
    if(profondeurMax==1&&n>1&&((double)rand()/((double)RAND_MAX+1.0))<0.35){
        best=coups[rand()%n]; *out=best; *scoreOut=0; return 1;
    }
    int couleurIA=(couleurHumain==BLANC)?NOIR:BLANC;
    int estMax=(joueurActuel==couleurIA);
    for(int i=0;i<n;i++) {
        UndoCoup u; appliquerCoupUndo(coups[i],plateau,&u);
        int encore=coups[i].info.prise&&coups[i].info.nbPrises>1;
        int prochainEstMax=encore?estMax:!estMax;
        uint64_t h=hashPlateau(plateau,joueurActuel^1,prochainEstMax);
        double s=minimax(plateau,profondeurMax-1,prochainEstMax,-INFINITY,INFINITY,h,joueurActuel^1);
        annulerCoupUndo(&u,plateau);
        if(s>bestScore){bestScore=s;best=coups[i];}
    }
    *out=best;*scoreOut=bestScore;return 1;
}

static void depuisFlat(const int8_t*flat,Plateau plat) {
    for(int x=0;x<TAILLE;x++)for(int z=0;z<TAILLE;z++){
        int8_t v=flat[x*TAILLE+z];
        plat[x][z]=(v==0)?(Case){BLANC,0}:(v==1)?(Case){BLANC,1}:(v==2)?(Case){NOIR,0}:(v==3)?(Case){NOIR,1}:(Case){VIDE,0};
    }
}

EMSCRIPTEN_KEEPALIVE
char* wasm_calculerMeilleurCoup(int8_t*flat,int joueurActuel,int profondeurMax,int couleurHumainParam) {
    static char buffer[220]; Plateau plateau; depuisFlat(flat,plateau);
    CoupComplet best; double score; int ok=trouverMeilleurCoup(plateau,joueurActuel,profondeurMax,couleurHumainParam,&best,&score);
    if(!ok){snprintf(buffer,sizeof(buffer),"{\"aucunCoup\":true}");}
    else snprintf(buffer,sizeof(buffer),"{\"x1\":%d,\"z1\":%d,\"x2\":%d,\"z2\":%d,\"prise\":%d,\"px\":%d,\"pz\":%d,\"score\":%g,\"nodes\":%llu,\"ttHits\":%llu}",best.x1,best.z1,best.x2,best.z2,best.info.prise,best.info.px,best.info.pz,score,(unsigned long long)nodesRecherche,(unsigned long long)ttHits);
    return buffer;
}

#ifndef __EMSCRIPTEN__
static void plateauInitial(Plateau p){for(int x=0;x<TAILLE;x++)for(int z=0;z<TAILLE;z++)p[x][z]=(Case){VIDE,0};for(int z=0;z<4;z++)for(int x=0;x<TAILLE;x++)if((x+z)%2==1)p[x][z]=(Case){NOIR,0};for(int z=6;z<10;z++)for(int x=0;x<TAILLE;x++)if((x+z)%2==1)p[x][z]=(Case){BLANC,0};}
int main(int argc,char**argv){const char*m=argc>1?argv[1]:"normal";int d=!strcmp(m,"faible")?1:!strcmp(m,"moyen")?3:!strcmp(m,"normal")?5:!strcmp(m,"expert")?7:0;if(!d)return 1;Plateau p;plateauInitial(p);CoupComplet c;double s;clock_t a=clock();int ok=trouverMeilleurCoup(p,NOIR,d,BLANC,&c,&s);clock_t b=clock();if(!ok)return 2;printf("{\"mode\":\"%s\",\"coup\":{%d,%d,%d,%d},\"score\":%g,\"tempsMs\":%.1f,\"nodes\":%llu,\"ttHits\":%llu}\n",m,c.x1,c.z1,c.x2,c.z2,s,1000.0*(double)(b-a)/CLOCKS_PER_SEC,(unsigned long long)nodesRecherche,(unsigned long long)ttHits);return 0;}
#endif
