/* Simulated annealing for order-K permutations of Z/nZ with few doubling breakpoints.
 *
 *   B(f) = #{x in Z/n : f(x+1) != 2 f(x) mod n},   f^K = id exactly.
 *
 * The cycle type is fixed at the start (c4 = number of K-cycles, c2 = number of 2-cycles when K=4,
 * rest fixed points) and preserved by the only move: conjugation f -> t f t with t a transposition.
 * Every conjugate has the same cycle type, so f^K = id holds throughout; it is re-verified at the end.
 *
 * Usage: anneal_breakpoints n K steps restarts seed [nfixed] [n2] [outfile]
 *   nfixed, n2: numbers of fixed points and 2-cycles (K=4 only); defaults: minimal.
 * Prints: n K best_B ratio  and writes best f (one line, space separated) to outfile if given.
 */
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>

static unsigned long long rs;
static inline unsigned long long rnd(void){ rs ^= rs<<13; rs ^= rs>>7; rs ^= rs<<17; return rs; }
static inline double urand(void){ return (rnd()>>11)*(1.0/9007199254740992.0); }

static int n, K;
static int *f, *finv;

static inline int bp(int v){ int w=(v+1)%n; return f[w] != (int)((2L*f[v])%n); }

long total(void){ long s=0; for(int v=0; v<n; v++) s+=bp(v); return s; }

int main(int argc, char **argv){
  if(argc<6){ fprintf(stderr,"usage\n"); return 1; }
  n=atoi(argv[1]); K=atoi(argv[2]); long long steps=atoll(argv[3]); int restarts=atoi(argv[4]);
  rs = strtoull(argv[5],0,10)*2654435761ULL + 88172645463325252ULL;
  int nfixed=-1, n2=0; const char *out=NULL;
  if(argc>6) nfixed=atoi(argv[6]);
  if(argc>7) n2=atoi(argv[7]);
  if(argc>8) out=argv[8];
  if(nfixed<0){ nfixed = n % K; if(K==4 && n%4==2){ nfixed=0; n2=1; } if(K==4 && n%4==3){ nfixed=1; n2=1; } }
  if((n - nfixed - 2*n2) % K != 0 || (K!=4 && n2)){ fprintf(stderr,"bad type\n"); return 1; }
  int cK = (n - nfixed - 2*n2)/K;
  f=malloc(sizeof(int)*n); finv=malloc(sizeof(int)*n);
  int *best=malloc(sizeof(int)*n); long bestB=1L<<60;
  int *perm=malloc(sizeof(int)*n);
  for(int r=0; r<restarts; r++){
    for(int i=0;i<n;i++) perm[i]=i;
    for(int i=n-1;i>0;i--){ int j=rnd()%(i+1); int t=perm[i]; perm[i]=perm[j]; perm[j]=t; }
    int p=0;
    for(int c=0;c<cK;c++){ for(int i=0;i<K;i++) f[perm[p+i]]=perm[p+(i+1)%K]; p+=K; }
    for(int c=0;c<n2;c++){ f[perm[p]]=perm[p+1]; f[perm[p+1]]=perm[p]; p+=2; }
    for(;p<n;p++) f[perm[p]]=perm[p];
    for(int i=0;i<n;i++) finv[f[i]]=i;
    long cur=total();
    double T0=2.0, T1=0.02;
    for(long long st=0; st<steps; st++){
      double T = T0*pow(T1/T0, (double)st/steps);
      int x=rnd()%n, y=rnd()%n; if(x==y) continue;
      int U[4]={x,y,finv[x],finv[y]}; int nu=0, Uu[4];
      for(int i=0;i<4;i++){ int dup=0; for(int j=0;j<nu;j++) if(Uu[j]==U[i]) dup=1; if(!dup) Uu[nu++]=U[i]; }
      int P[8]; int np=0;
      for(int i=0;i<nu;i++){ int a=(Uu[i]-1+n)%n, b=Uu[i];
        int d=0; for(int j=0;j<np;j++) if(P[j]==a) d=1; if(!d) P[np++]=a;
        d=0; for(int j=0;j<np;j++) if(P[j]==b) d=1; if(!d) P[np++]=b; }
      int old=0; for(int j=0;j<np;j++) old+=bp(P[j]);
      int ov[4], nv[4];
      for(int i=0;i<nu;i++){ int u=Uu[i]; int tu = u==x? y : (u==y? x : u); int v=f[tu]; nv[i]= v==x? y : (v==y? x : v); ov[i]=f[u]; }
      for(int i=0;i<nu;i++) f[Uu[i]]=nv[i];
      int nw=0; for(int j=0;j<np;j++) nw+=bp(P[j]);
      int delta=nw-old;
      if(delta<=0 || urand() < exp(-delta/T)){
        for(int i=0;i<nu;i++) finv[nv[i]]=Uu[i];
        cur+=delta;
        if(cur<bestB){ bestB=cur; memcpy(best,f,sizeof(int)*n); }
      } else {
        for(int i=0;i<nu;i++) f[Uu[i]]=ov[i];
      }
    }
  }
  /* verify */
  memcpy(f,best,sizeof(int)*n);
  char *seen=calloc(n,1); for(int i=0;i<n;i++){ if(seen[f[i]]){ printf("NOT A PERMUTATION\n"); return 2;} seen[f[i]]=1; }
  for(int x=0;x<n;x++){ int y=x; for(int i=0;i<K;i++) y=f[y]; if(y!=x){ printf("ORDER FAIL\n"); return 2; } }
  long vb=total();
  printf("%d %d %ld %.5f fixed=%d two=%d\n", n, K, vb, (double)vb/n, nfixed, n2);
  if(out){ FILE *fh=fopen(out,"w"); for(int i=0;i<n;i++) fprintf(fh,"%d ",best[i]); fprintf(fh,"\n"); fclose(fh); }
  return 0;
}
