/* Minimum-percolating-set heuristics for the 2-of-3 fold rule on the
   triples T_g = (g, A[g], B[g]) of a finite L-set Q, L = F(a,b).
   Input (binary, stdin): int32 n, int32 A[n], int32 B[n]  (A[g] = a.g, B[g] = b.g).
   Usage: perc TRIALS RNGSEED PRUNE
   Output: best seed count s, s/n, and a from-scratch verification of the best set.
   Every reported s is certified: the set is re-closed from scratch and must cover Q. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int n, *A, *B, *Ainv, *Binv;
static unsigned long long rs;
static unsigned rnd(void){ rs ^= rs<<13; rs ^= rs>>7; rs ^= rs<<17; return (unsigned)(rs>>11); }

/* triple t has slots t, A[t], B[t]; vertex v occurs in triples v, Ainv[v], Binv[v] */
static int slot(int t,int k){ return k==0?t:(k==1?A[t]:B[t]); }

static char *inf; static unsigned char *cnt; static int *queue;

/* close from current state; returns number infected */
static long closeq(int qh,int qt,long ninf){
  while(qh<qt){ int v=queue[qh++]; int ts[3]={v,Ainv[v],Binv[v]};
    for(int k=0;k<3;k++){ int t=ts[k];
      /* count multiplicity: v may occupy several slots of t; handled by recount */
      int c=0; for(int j=0;j<3;j++) c+=inf[slot(t,j)];
      if(c==2){ for(int j=0;j<3;j++){ int w=slot(t,j); if(!inf[w]){ inf[w]=1; ninf++; queue[qt++]=w; } } }
    } }
  return ninf;
}
static long closure_of(const char *seed){
  memset(inf,0,n); int qt=0; long ni=0;
  for(int v=0;v<n;v++) if(seed[v]){ inf[v]=1; ni++; queue[qt++]=v; }
  return closeq(0,qt,ni);
}
/* score of uninfected v: number of its triples that would reach count >= 2 */
static int score(int v){ int ts[3]={v,Ainv[v],Binv[v]}; int s=0;
  for(int k=0;k<3;k++){ int t=ts[k]; int c=0,cv=0; for(int j=0;j<3;j++){ int w=slot(t,j); c+=inf[w]; cv+=(w==v);} if(c+cv>=2 && c<2) s++; }
  return s; }

int main(int argc,char**argv){
  int trials=argc>1?atoi(argv[1]):5; rs=argc>2?strtoull(argv[2],0,10)*2654435761ULL+1:88172645463325252ULL; int prune=argc>3?atoi(argv[3]):1;
  if(fread(&n,4,1,stdin)!=1) return 1;
  A=malloc(4*n);B=malloc(4*n);Ainv=malloc(4*n);Binv=malloc(4*n);
  if(fread(A,4,n,stdin)!=(size_t)n||fread(B,4,n,stdin)!=(size_t)n) return 1;
  for(int v=0;v<n;v++){Ainv[A[v]]=v;Binv[B[v]]=v;}
  inf=malloc(n); queue=malloc(4*(size_t)n*3+16); char *seed=malloc(n), *best=malloc(n); long bests=-1;
  int *order=malloc(4*n);
  for(int tr=0;tr<trials;tr++){
    memset(inf,0,n); memset(seed,0,n); long ni=0, s=0;
    for(int v=0;v<n;v++) order[v]=v;
    for(int v=n-1;v>0;v--){ int j=rnd()%(v+1); int x=order[v];order[v]=order[j];order[j]=x; }
    /* greedy: prefer uninfected vertices of max score; scan in random order with restarts */
    int pos=0;
    while(ni<n){
      int bv=-1,bsc=-1, looked=0;
      for(int k=0;k<n && looked<64;k++){ int v=order[(pos+k)%n]; if(inf[v]) continue; looked++; int sc=score(v); if(sc>bsc){bsc=sc;bv=v; if(sc==3) break;} }
      pos=(pos+ (int)(rnd()%n))%n;
      seed[bv]=1; s++; inf[bv]=1; ni++; queue[0]=bv; ni=closeq(0,1,ni);
    }
    if(prune){ /* drop redundant seeds */
      for(int k=0;k<n;k++){ int v=order[k]; if(!seed[v]) continue; seed[v]=0; if(closure_of(seed)<n) seed[v]=1; else s--; }
    }
    if(closure_of(seed)!=n){ fprintf(stderr,"BUG\n"); return 2; }
    if(bests<0||s<bests){ bests=s; memcpy(best,seed,n); }
    fprintf(stderr,"trial %d s=%ld ratio=%.5f\n",tr,s,(double)s/n);
  }
  long ver=closure_of(best);
  printf("n=%d best_s=%ld ratio=%.5f verified_closure=%ld\n",n,bests,(double)bests/n,ver);
  return 0;
}
