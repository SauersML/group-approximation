/* theta_chain.c -- exact per-sample evaluation of the bisector-chain
 * denominators Theta^-(S) = P_{S^-}(D^-) for bond percolation on Z^2,
 * box proxy B_n = [-n,n]^2 with target the box boundary.
 *
 * Straight path on the x-axis, cut edge (0,0)(1,0), U^- = {(a,0): a<=0},
 * L = dual edges with midpoint first coordinate < 1/2 (Lemma 0.1 of
 * fpbs-bisector-split-chain-caps-at-inverse-theta-squared-proof).
 *
 * D^-(S) fails iff some dual-open circuit (duals of closed edges of B_n,
 * duals of the declared-open pattern edges removed) surrounds a vertex of
 * V(S^-) and contains a dual edge with midpoint a >= 1/2.
 *
 * Exact algorithm (see the proof note, Lemma 2.1):
 *  (1) biconnected components (blocks) of the dual-open graph;
 *  (2) G_N = union of the blocks that contain a non-L edge;
 *  (3) a vertex is surrounded by a circuit through a non-L edge iff it is
 *      not reached by a primal flood from the box boundary that never
 *      crosses an edge of G_N.
 *
 * Configurations (all share one sample of omega):
 *   0 PHI   : no pattern, all vertices (a,0), -n < a <= 0     (pattern-free lower bound)
 *   1 DY2   : edges (-2^j,0)(-2^j+1,0), j>=0                  (dyadic b=2, contains e_{k-1})
 *   2 DY2F  : same with j>=1 (fingers only, (0,0) not a pattern vertex)
 *   3 DY4   : edges (-4^j,0)(-4^j+1,0), j>=0
 *   4 ALT   : edges (-2i-1,0)(-2i,0), i>=0                     (alternating, dense)
 * plus PI = P((0,0) <-> boundary), the theta proxy.
 *
 * Usage: theta_chain n samples seed [p]      (p = primal open prob, default 0.5)
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>

static uint64_t rs;
static inline uint64_t xr(void){ rs^=rs<<13; rs^=rs>>7; rs^=rs<<17; return rs; }

static int n, W;            /* primal coords -n..n, W = 2n+1 */
static int DW;              /* dual coords: dual vertex (i+1/2, j+1/2), i,j in -n-1..n -> DW = 2n+2 */
static unsigned char *hopen, *vopen; /* primal edge open: h[(x,y)] = (x,y)-(x+1,y); v = (x,y)-(x,y+1) */
static unsigned char *hdecl, *vdecl; /* declared open (pattern) */
#define PIDX(x,y) (((y)+n)*W + ((x)+n))
#define DIDX(i,j) (((j)+n+1)*DW + ((i)+n+1))

/* dual edges: the dual of primal h-edge (x,y)-(x+1,y) is vertical, joining
 * dual (x,y-1) [= (x+1/2,y-1/2)] and dual (x,y) [= (x+1/2,y+1/2)]; midpoint a = x+1/2.
 * The dual of primal v-edge (x,y)-(x,y+1) is horizontal, joining dual (x-1,y)
 * and dual (x,y); midpoint a = x.  Non-L means midpoint a >= 1/2:
 * h-edge: x >= 0 ; v-edge: x >= 1. */

/* dual edge ids: 2*PIDX + 0 (h) / 1 (v) */
static int ND, NE;
static int *dfsnum, *low, *estack, *vstack, *itstack, *blockmark, *eblock;
static unsigned char *enn;     /* edge in G_N */
static unsigned char *reach;
static int *queue;

static inline int dual_open(int pe){ /* pe = 2*pidx + t */
  int t = pe & 1, pi = pe >> 1;
  if (t==0) return !hopen[pi] && !hdecl[pi];
  return !vopen[pi] && !vdecl[pi];
}
/* existence of primal edge in box */
static inline int pedge_exists(int x,int y,int t){
  if (x<-n||x>n||y<-n||y>n) return 0;
  if (t==0) return x < n;
  return y < n;
}
/* list incident dual edges of dual vertex (i,j): up to 4 */
static int dnbr(int i,int j,int *ev,int *vv){
  int c=0;
  /* vertical dual edge up: dual (i,j)-(i,j+1) is dual of primal h-edge (i,j+1) */
  if (pedge_exists(i,j+1,0)){ int pe=2*PIDX(i,j+1); if(dual_open(pe)){ev[c]=pe; vv[c]=DIDX(i,j+1); c++;} }
  /* down: dual (i,j-1)-(i,j) is dual of primal h-edge (i,j) */
  if (pedge_exists(i,j,0)){ int pe=2*PIDX(i,j); if(dual_open(pe)){ev[c]=pe; vv[c]=DIDX(i,j-1); c++;} }
  /* right: dual (i,j)-(i+1,j) is dual of primal v-edge (i+1,j) */
  if (pedge_exists(i+1,j,1)){ int pe=2*PIDX(i+1,j)+1; if(dual_open(pe)){ev[c]=pe; vv[c]=DIDX(i+1,j); c++;} }
  /* left: dual (i-1,j)-(i,j) is dual of primal v-edge (i,j) */
  if (pedge_exists(i,j,1)){ int pe=2*PIDX(i,j)+1; if(dual_open(pe)){ev[c]=pe; vv[c]=DIDX(i-1,j); c++;} }
  return c;
}
static inline int nonL(int pe){
  int t=pe&1, pi=pe>>1; int x = pi % W - n;
  return t==0 ? (x>=0) : (x>=1);
}

static int *pedge_of;   /* parent edge of dual vertex in DFS */
static unsigned char *itpos;

/* mark G_N: union of blocks of the dual-open graph containing a non-L edge */
static void blocks(void){
  memset(dfsnum,0,sizeof(int)*ND);
  memset(enn,0,NE);
  int cnt=0, ev[4], vv[4];
  for (int r=0;r<ND;r++){
    if (dfsnum[r]) continue;
    int sp=0, ep=0;
    vstack[sp++]=r; dfsnum[r]=low[r]=++cnt; pedge_of[r]=-1; itpos[r]=0;
    while (sp){
      int v=vstack[sp-1];
      int i=v%DW-n-1, j=v/DW-n-1;
      int c=dnbr(i,j,ev,vv);
      if (itpos[v]<c){
        int k=itpos[v]++; int e=ev[k], w=vv[k];
        if (e==pedge_of[v]) continue;
        if (!dfsnum[w]){
          estack[ep++]=e; pedge_of[w]=e; dfsnum[w]=low[w]=++cnt; itpos[w]=0; vstack[sp++]=w;
        } else if (dfsnum[w]<dfsnum[v]){
          estack[ep++]=e; if (dfsnum[w]<low[v]) low[v]=dfsnum[w];
        }
      } else {
        sp--;
        if (sp){
          int u=vstack[sp-1];
          if (low[v]<low[u]) low[u]=low[v];
          if (low[v]>=dfsnum[u]){
            int pos=ep-1; while (estack[pos]!=pedge_of[v]) pos--;
            int flag=0; for (int q=pos;q<ep;q++) if (nonL(estack[q])){flag=1;break;}
            if (flag) for (int q=pos;q<ep;q++) enn[estack[q]]=1;
            ep=pos;
          }
        }
      }
    }
  }
}

/* primal flood from the box boundary, never crossing an edge of G_N */
static void flood(void){
  memset(reach,0,W*W);
  int qh=0, qt=0;
  for (int x=-n;x<=n;x++) for (int y=-n;y<=n;y++)
    if (x==-n||x==n||y==-n||y==n){ int p=PIDX(x,y); reach[p]=1; queue[qt++]=p; }
  while (qh<qt){
    int p=queue[qh++]; int x=p%W-n, y=p/W-n;
    /* right: h-edge (x,y) */
    if (x<n && !enn[2*p] && !reach[p+1]){ reach[p+1]=1; queue[qt++]=p+1; }
    if (x>-n && !enn[2*(p-1)] && !reach[p-1]){ reach[p-1]=1; queue[qt++]=p-1; }
    if (y<n && !enn[2*p+1] && !reach[p+W]){ reach[p+W]=1; queue[qt++]=p+W; }
    if (y>-n && !enn[2*(p-W)+1] && !reach[p-W]){ reach[p-W]=1; queue[qt++]=p-W; }
  }
}

static int origin_to_boundary(void){
  memset(reach,0,W*W);
  int qh=0,qt=0,p0=PIDX(0,0); reach[p0]=1; queue[qt++]=p0;
  while (qh<qt){
    int p=queue[qh++]; int x=p%W-n, y=p/W-n;
    if (x==-n||x==n||y==-n||y==n) return 1;
    if (hopen[p] && !reach[p+1]){reach[p+1]=1;queue[qt++]=p+1;}
    if (hopen[p-1] && !reach[p-1]){reach[p-1]=1;queue[qt++]=p-1;}
    if (vopen[p] && !reach[p+W]){reach[p+W]=1;queue[qt++]=p+W;}
    if (vopen[p-W] && !reach[p-W]){reach[p-W]=1;queue[qt++]=p-W;}
  }
  return 0;
}

#define NC 5
static const char *cname[NC]={"PHI","DY2","DY2F","DY4","ALT"};

/* set pattern for configuration c; fill list of vertices to check (x-coords, y=0) */
static int setpat(int c, int *chk){
  memset(hdecl,0,W*W);
  int m=0;
  if (c==0){ for (int a=0;a>-n;a--) chk[m++]=a; return m; }
  int base = (c==3)?4:2;
  if (c==1||c==2||c==3){
    long r = (c==2)?base:1;
    for (; r<n; r*=base){ int x=(int)(-r); hdecl[PIDX(x,0)]=1; chk[m++]=x; chk[m++]=x+1; }
    return m;
  }
  for (int i=0; 2*i+1<n; i++){ int x=-2*i-1; hdecl[PIDX(x,0)]=1; chk[m++]=x; chk[m++]=x+1; }
  return m;
}

int main(int argc,char**argv){
  if (argc<4){ fprintf(stderr,"usage: %s n samples seed [p]\n",argv[0]); return 1; }
  n=atoi(argv[1]); long S=atol(argv[2]); rs=0x9E3779B97F4A7C15ULL^(uint64_t)atoll(argv[3])*0x2545F4914F6CDD1DULL; if(!rs) rs=1;
  double p = argc>4 ? atof(argv[4]) : 0.5;
  W=2*n+1; DW=2*n+2; ND=DW*DW; NE=2*W*W;
  hopen=calloc(W*W,1); vopen=calloc(W*W,1); hdecl=calloc(W*W,1); vdecl=calloc(W*W,1);
  dfsnum=malloc(sizeof(int)*ND); low=malloc(sizeof(int)*ND); vstack=malloc(sizeof(int)*ND);
  pedge_of=malloc(sizeof(int)*ND); itpos=malloc(ND); estack=malloc(sizeof(int)*NE);
  enn=malloc(NE); reach=malloc(W*W); queue=malloc(sizeof(int)*W*W);
  int *chk=malloc(sizeof(int)*4*W);
  uint64_t thr=(uint64_t)(p*18446744073709551615.0);
  const int NB=20; long cntb[NB][NC+1]; memset(cntb,0,sizeof cntb); long nb[NB]; memset(nb,0,sizeof nb);
  for (long s=0;s<S;s++){
    for (int q=0;q<W*W;q++){ hopen[q]=xr()<thr; vopen[q]=xr()<thr; }
    int b=s%NB; nb[b]++;
    cntb[b][NC]+=origin_to_boundary();
    for (int c=0;c<NC;c++){
      int m=setpat(c,chk);
      blocks(); flood();
      int ok=1; for (int k=0;k<m;k++) if (!reach[PIDX(chk[k],0)]){ok=0;break;}
      cntb[b][c]+=ok;
    }
  }
  /* jackknife */
  printf("# n=%d samples=%ld p=%.4f\n",n,S,p);
  for (int c=0;c<=NC;c++){
    long tot=0,T=0; for(int b=0;b<NB;b++){tot+=cntb[b][c];T+=nb[b];}
    double est=(double)tot/T, v=0;
    for(int b=0;b<NB;b++){ double e=(double)(tot-cntb[b][c])/(T-nb[b]); v+=(e-est)*(e-est);} v*= (NB-1.0)/NB;
    printf("%-5s %.6f %.6f\n", c<NC?cname[c]:"PI", est, sqrt(v));
  }
  return 0;
}
