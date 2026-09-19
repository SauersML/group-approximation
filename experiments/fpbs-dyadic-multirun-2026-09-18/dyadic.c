/* Multi-scale sparse patterns for the coverage decorrelation constant
 * K(S) = q(S) / (q(S^-) q(S^+)) on the straight Z^2 path, box proxy.
 *
 * Box [-M,M]^2, target = boundary of the box.  Path = x-axis.  Cut edge
 * e_k = (0,0)-(1,0) (Bernoulli, never declared).  For base b and depth J the
 * pattern S_{b,J} consists of the single edges
 *     left : (-b^j, 0) - (-b^j + 1, 0)      j = 0..J-1
 *     right: ( b^j + ... ) mirrored: (1 + b^j, 0) - (b^j, 0)    j = 0..J-1
 * i.e. the pattern is symmetric under the reflection x -> 1 - x which swaps
 * U^- = {x <= 0} and U^+ = {x >= 1}.  Consecutive pattern edges are separated
 * by gaps (b >= 2 and j >= 1 give distinct non-adjacent edges except the pair
 * j=0,1 for b=2, which are at offsets 1 and 2: edges (-1,0)(0,0) and
 * (-2,0)(-1,0) are adjacent -> one run; this is harmless).
 *
 * q(F) = P(every vertex of V(F) is joined to the boundary | F declared open).
 * (For a declared-open run, one endpoint joined <=> the run joined.)
 * All three quantities q(S), q(S^-), q(S^+) are computed from the same sample:
 * every candidate edge is held out of the bulk union-find, and each event is
 * decided on the contracted graph of bulk components.
 *
 * Also reported: theta = P((0,0) <-> boundary) (all edges Bernoulli) and the
 * two-point kernel K_1 of the pattern {e_{k-1}, e_{k+1}}.
 *
 * usage: dyadic p M samples seed base Jmax
 * Output: for J=1..Jmax: J, qS, qA, qB, K, K*theta, jackknife se (20 batches).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>

static uint64_t s[2];
static inline uint64_t rotl(uint64_t x, int k){return (x<<k)|(x>>(64-k));}
static inline uint64_t nxt(void){uint64_t s0=s[0],s1=s[1],r=s0+s1;s1^=s0;s[0]=rotl(s0,55)^s1^(s1<<14);s[1]=rotl(s1,36);return r;}
static inline double unif(void){return (nxt()>>11)*(1.0/9007199254740992.0);}

static int *par;
static int fnd(int x){while(par[x]!=x){par[x]=par[par[x]];x=par[x];}return x;}
static void uni(int a,int b){a=fnd(a);b=fnd(b);if(a!=b)par[a]=b;}

#define MAXE 64
#define NB 20
int ne;                 /* number of held-out candidate edges */
int ex[MAXE];           /* left endpoint x-coordinate of held-out edge (edge (x,0)-(x+1,0)) */
int side[MAXE];         /* -1 left, +1 right */
int lev[MAXE];          /* scale index j */
int st[MAXE];           /* sampled state */
int ra[MAXE], rb2[MAXE];/* bulk roots of endpoints */

/* small UF over bulk roots: map roots to 0..2ne via linear table */
static int key[2*MAXE+2], nk;
static int sp[2*MAXE+2];
static int sf(int x){while(sp[x]!=x){sp[x]=sp[sp[x]];x=sp[x];}return x;}
static int idx(int r){for(int i=0;i<nk;i++) if(key[i]==r) return i; key[nk]=r; sp[nk]=nk; return nk++;}

/* mode: 0 = S (both sides declared), 1 = S^- only, 2 = S^+ only.
 * J: depth.  Returns 1 iff every declared edge's endpoint joined to boundary. */
static int bndroot;
static int event(int mode,int J){
  nk=0; int B=idx(bndroot);
  int decl[MAXE];
  for(int e=0;e<ne;e++){
    int in = lev[e]<J && ((mode==0) || (mode==1 && side[e]<0) || (mode==2 && side[e]>0));
    decl[e]=in;
    int a=idx(ra[e]), b=idx(rb2[e]);
    if(in || st[e]){ a=sf(a); b=sf(b); if(a!=b) sp[a]=b; }
  }
  int bb=sf(B);
  for(int e=0;e<ne;e++) if(decl[e]){ if(sf(idx(ra[e]))!=bb) return 0; }
  return 1;
}

int main(int argc,char**argv){
  if(argc<7){fprintf(stderr,"usage: dyadic p M samples seed base Jmax\n");return 1;}
  double p=atof(argv[1]); int M=atoi(argv[2]); long S=atol(argv[3]); long seed=atol(argv[4]);
  int base=atoi(argv[5]); int Jmax=atoi(argv[6]);
  s[0]=0x9E3779B97F4A7C15ULL^seed; s[1]=0xD1B54A32D192ED03ULL+seed*7919; for(int i=0;i<20;i++)nxt();
  /* build candidate edges */
  ne=0; long off=1;
  for(int j=0;j<Jmax;j++){
    if(off+1>=M){fprintf(stderr,"Jmax too large for M\n");return 1;}
    /* left edge (-off,0)-(-off+1,0): left endpoint x=-off */
    int dup=0; for(int e=0;e<ne;e++) if(ex[e]==-off) dup=1;
    if(!dup){ ex[ne]=-off; side[ne]=-1; lev[ne]=j; ne++; }
    /* right mirror under x->1-x: edge (1+off-1,0)-(1+off,0) : left endpoint x=off */
    dup=0; for(int e=0;e<ne;e++) if(ex[e]==off) dup=1;
    if(!dup){ ex[ne]=off; side[ne]=+1; lev[ne]=j; ne++; }
    off*=base;
  }
  int W=2*M+1, NV=W*W, BND=NV;
  par=malloc(sizeof(int)*(NV+1));
  #define V(x,y) (((y)+M)*W+((x)+M))
  double cnt[NB][MAXE][3]; double th[NB]; memset(cnt,0,sizeof cnt); memset(th,0,sizeof th);
  for(long sm=0;sm<S;sm++){
    int bt=sm%NB;
    for(int v=0;v<=NV;v++)par[v]=v;
    for(int y=-M;y<=M;y++)for(int x=-M;x<=M;x++){
      int v=V(x,y);
      if(x==-M||y==-M||x==M||y==M) uni(v,BND);
      if(x<M){
        int held=-1;
        if(y==0) for(int e=0;e<ne;e++) if(ex[e]==x) held=e;
        if(held>=0) st[held]=(unif()<p);
        else if(unif()<p) uni(v,v+1);
      }
      if(y<M){ if(unif()<p) uni(v,v+W); }
    }
    bndroot=fnd(BND);
    for(int e=0;e<ne;e++){ ra[e]=fnd(V(ex[e],0)); rb2[e]=fnd(V(ex[e]+1,0)); }
    /* theta: (0,0) joined to boundary with held edges at sampled state */
    { nk=0; int B=idx(bndroot);
      for(int e=0;e<ne;e++){ int a=idx(ra[e]), b=idx(rb2[e]); if(st[e]){a=sf(a);b=sf(b);if(a!=b)sp[a]=b;} }
      int o=idx(fnd(V(0,0))); th[bt]+= (sf(o)==sf(B)); }
    for(int J=1;J<=Jmax;J++) for(int c=0;c<3;c++) cnt[bt][J][c]+=event(c,J);
  }
  double per=(double)S/NB;
  double thT=0; for(int b=0;b<NB;b++)thT+=th[b]; thT/=S;
  printf("# p=%g M=%d base=%d samples=%ld theta_proxy=%.5f\n",p,M,base,S,thT);
  printf("# J  qS qA qB  K  K*theta  se(K) se(K*theta)\n");
  for(int J=1;J<=Jmax;J++){
    double T[3]={0,0,0}; for(int b=0;b<NB;b++)for(int c=0;c<3;c++)T[c]+=cnt[b][J][c];
    double q[3]; for(int c=0;c<3;c++) q[c]=T[c]/S;
    double K=q[0]/(q[1]*q[2]), KT=K*thT;
    double js=0,js2=0,jt=0,jt2=0;
    for(int b=0;b<NB;b++){
      double qq[3]; for(int c=0;c<3;c++) qq[c]=(T[c]-cnt[b][J][c])/(S-per);
      double tb=(thT*S-th[b])/(S-per);
      double Kb=qq[0]/(qq[1]*qq[2]); js+=Kb; js2+=Kb*Kb; jt+=Kb*tb; jt2+=Kb*tb*Kb*tb;
    }
    js/=NB; js2/=NB; jt/=NB; jt2/=NB;
    double se=sqrt((NB-1)*(js2-js*js)), set=sqrt((NB-1)*(jt2-jt*jt));
    printf("%2d %.6f %.6f %.6f %.4f %.4f %.4f %.4f\n",J,q[0],q[1],q[2],K,KT,se,set);
  }
  return 0;
}
