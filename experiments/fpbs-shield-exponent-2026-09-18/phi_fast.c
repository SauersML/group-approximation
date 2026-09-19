/* phi_fast.c -- linear-time exact evaluation of D^-(U^-) (the pattern-free
 * event Phi of fpbs-bisector-chain-is-polynomial-in-inverse-theta) for
 * Bernoulli(p) bond percolation on Z^2, box proxies B_n = [-n,n]^2 with the
 * box boundary as target, for the nested boxes n = N, N/2, ..., NMIN of ONE
 * configuration on B_N.
 *
 * Criterion (pinch-wall theorem, Theorem B in Section 2 of
 * research/fpbs-geodesic-bisector-chain-polynomial-in-inverse-theta-proof.md):
 *   I_n   = vertices joined to dB_n inside B_n (dB_n wired);
 *   walls = edges with both ends in I_n (open or closed), and the diagonals
 *           of unit plaquettes whose two opposite corners are both in I_n;
 *   D^-_n fails  iff  some v=(a,0), -n<a<=0, v notin I_n, lies in a face of
 *           the wall arrangement that contains a piece of a plaquette with
 *           centre abscissa >= 1/2.
 * Faces are computed by a flood over plaquette quarter-triangles.
 * The configuration generator is identical to theta_chain.c, so for n = N the
 * per-sample outcome can be compared with the block (Tarjan) algorithm there.
 *
 * Usage: phi_fast N samples seed [p] [NMIN] [verbose]
 * Output: for every n: P(D_n), P(0 in I_n), P(D_n | D_{n/2}) with jackknife errors.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>

static uint64_t rs;
static inline uint64_t xr(void){ rs^=rs<<13; rs^=rs>>7; rs^=rs<<17; return rs; }

static int N, W;                       /* coordinates -N..N, W = 2N+1 */
static unsigned char *hopen, *vopen;   /* h: (x,y)-(x+1,y), v: (x,y)-(x,y+1) */
static unsigned char *inI;             /* vertex in I_n */
static unsigned char *mark;            /* triangle reached */
static int *queue;
#define PIDX(x,y) (((y)+N)*W + ((x)+N))
/* plaquette (i,j) = centre (i+1/2, j+1/2), i,j in -N..N-1, index on the same W grid */
#define TIDX(i,j,t) (4*PIDX(i,j)+(t))

/* I_n by BFS from dB_n over open edges inside B_n */
static void compute_I(int n){
  for (int y=-n;y<=n;y++) memset(inI+PIDX(-n,y),0,2*n+1);
  int qh=0, qt=0;
  for (int x=-n;x<=n;x++) for (int y=-n;y<=n;y++)
    if (x==-n||x==n||y==-n||y==n){ int p=PIDX(x,y); inI[p]=1; queue[qt++]=p; }
  while (qh<qt){
    int p=queue[qh++]; int x=p%W-N, y=p/W-N;
    if (x<n  && hopen[p]   && !inI[p+1]){ inI[p+1]=1; queue[qt++]=p+1; }
    if (x>-n && hopen[p-1] && !inI[p-1]){ inI[p-1]=1; queue[qt++]=p-1; }
    if (y<n  && vopen[p]   && !inI[p+W]){ inI[p+W]=1; queue[qt++]=p+W; }
    if (y>-n && vopen[p-W] && !inI[p-W]){ inI[p-W]=1; queue[qt++]=p-W; }
  }
}

/* triangles: 0 top, 1 right, 2 bottom, 3 left */
static inline void push(int t, int *qt){ if(!mark[t]){ mark[t]=1; queue[(*qt)++]=t; } }

static int eval_D(int n){
  compute_I(n);
  for (int j=-n;j<n;j++) memset(mark+TIDX(-n,j,0),0,4*(2*n));
  int qh=0, qt=0;
  for (int j=-n;j<n;j++) for (int i=0;i<n;i++) for (int t=0;t<4;t++) push(TIDX(i,j,t),&qt);
  while (qh<qt){
    int T=queue[qh++]; int t=T&3, q=T>>2; int i=q%W-N, j=q/W-N;
    int sw=inI[PIDX(i,j)], se=inI[PIDX(i+1,j)], nw=inI[PIDX(i,j+1)], ne=inI[PIDX(i+1,j+1)];
    int dA = sw&&ne;   /* diagonal SW-NE wall: blocks top-right and bottom-left */
    int dB = nw&&se;   /* diagonal NW-SE wall: blocks right-bottom and left-top */
    switch(t){
      case 0: /* top */
        if(!dA) push(4*q+1,&qt);
        if(!dB) push(4*q+3,&qt);
        if(j+1<n && !(nw&&ne)) push(TIDX(i,j+1,2),&qt);
        break;
      case 1: /* right */
        if(!dA) push(4*q+0,&qt);
        if(!dB) push(4*q+2,&qt);
        if(i+1<n && !(se&&ne)) push(TIDX(i+1,j,3),&qt);
        break;
      case 2: /* bottom */
        if(!dA) push(4*q+3,&qt);
        if(!dB) push(4*q+1,&qt);
        if(j-1>=-n && !(sw&&se)) push(TIDX(i,j-1,0),&qt);
        break;
      case 3: /* left */
        if(!dA) push(4*q+2,&qt);
        if(!dB) push(4*q+0,&qt);
        if(i-1>=-n && !(sw&&nw)) push(TIDX(i-1,j,1),&qt);
        break;
    }
  }
  int full=1, half=1;
  for (int a=0;a>-n;a--){
    if (inI[PIDX(a,0)]) continue;
    if (mark[TIDX(a,0,2)]){ full=0; if (2*a>-n) half=0; }  /* bottom triangle of plaquette (a,0) touches v=(a,0) */
  }
  return full | (half<<1);
}

int main(int argc,char**argv){
  if (argc<4){ fprintf(stderr,"usage: %s N samples seed [p] [NMIN] [verbose]\n",argv[0]); return 1; }
  N=atoi(argv[1]); long S=atol(argv[2]);
  rs=0x9E3779B97F4A7C15ULL^(uint64_t)atoll(argv[3])*0x2545F4914F6CDD1DULL; if(!rs) rs=1;
  double p = argc>4 ? atof(argv[4]) : 0.5;
  int NMIN = argc>5 ? atoi(argv[5]) : N;
  int verbose = argc>6 ? atoi(argv[6]) : 0;
  W=2*N+1;
  hopen=calloc((size_t)W*W,1); vopen=calloc((size_t)W*W,1); inI=calloc((size_t)W*W,1);
  mark=calloc((size_t)4*W*W,1); queue=malloc(sizeof(int)*(size_t)4*W*W);
  uint64_t thr=(uint64_t)(p*18446744073709551615.0);
  int ns=0, sc[32]; for (int n=N; n>=NMIN && n>=2; n/=2) sc[ns++]=n;
  const int NB=20;
  static long cD[20][32], cI[20][32], cJ[20][32], nb[20]; long viol=0;
  for (long s=0;s<S;s++){
    for (long q=0;q<(long)W*W;q++){ hopen[q]=xr()<thr; vopen[q]=xr()<thr; }
    int b=s%NB; nb[b]++;
    int prevD=-1;
    char line[256]; int lp=0;
    for (int k=ns-1;k>=0;k--){           /* small to large */
      int n=sc[k];
      int dd=eval_D(n); int d=dd&1;
      cD[b][k]+=d; cI[b][k]+=inI[PIDX(0,0)];
      if (prevD>=0){ cJ[b][k]+= (d && prevD); if (d && !prevD) viol++; }
      prevD=d;
      if (verbose) lp+=sprintf(line+lp,"%d",d+2*((dd>>1)&1)+4*inI[PIDX(0,0)]);
    }
    if (verbose) printf("S %ld %s\n",s,line);
  }
  printf("# N=%d samples=%ld p=%.4f monotonicity_violations=%ld\n",N,S,p,viol);
  printf("# n   Phi        err       PI         err       P(D_n|D_n/2)  err\n");
  for (int k=ns-1;k>=0;k--){
    long T=0,tD=0,tI=0,tJ=0,tP=0;
    for(int b=0;b<NB;b++){T+=nb[b];tD+=cD[b][k];tI+=cI[b][k];tJ+=cJ[b][k]; if(k<ns-1) tP+=cD[b][k+1];}
    double eD=(double)tD/T, eI=(double)tI/T, eR = (k<ns-1 && tP)? (double)tJ/tP : NAN;
    double vD=0,vI=0,vR=0;
    for(int b=0;b<NB;b++){
      double a=(double)(tD-cD[b][k])/(T-nb[b]); vD+=(a-eD)*(a-eD);
      double c=(double)(tI-cI[b][k])/(T-nb[b]); vI+=(c-eI)*(c-eI);
      if (k<ns-1){ double r=(double)(tJ-cJ[b][k])/(tP-cD[b][k+1]); vR+=(r-eR)*(r-eR); }
    }
    double f=(NB-1.0)/NB;
    printf("%5d %.6f %.6f %.6f %.6f %.6f %.6f\n",sc[k],eD,sqrt(vD*f),eI,sqrt(vI*f),eR,sqrt(vR*f));
  }
  return 0;
}
