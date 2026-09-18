/* Exhaustive search for Bigelow pairs in D_n (Bigelow, GT 3 (1999), Thm 1.4):
 *   alpha embedded arc q1 -> q2, beta0 straight arc p0 -> q3, minimal position with m
 *   crossings (no bigons), and pairing  sum_k eps_k t^{e_k} = 0.
 * Configurations are enumerated modulo Stab(beta0) as crossing sequences in the cut disk D'.
 * Objects carry a height rank; boundary positions: L(r)=r+1, notch=NOTCH, R(r)=2*NOTCH-(r+1),
 * J = -1 (never enclosed).  Object 0 = first crossing (q1 sits at its L copy x0);
 * object 1 = q2 marker = last crossing's departure point (exact); objects 2..n-2 = free
 * punctures (q4..qn), each on J or at a side gap.
 * usage: arcpairs n m_min m_max [printhits]
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define MAXO 1024
#define NOTCH 4096
static int n, M, printhits;
static int rnk[MAXO], nobj;           /* ranks of height objects */
static int fside[8], fobj[8], nfree;   /* free punctures: side -1=J, 0=L, 1=R */
static int q2side;                     /* side of departure point y (q2 there) */
/* crossing k (k=0..m-1): object id cobj[k], arrival side cs[k] */
static int cobj[MAXO], cs[MAXO];
static int chA[MAXO], chB[MAXO];      /* chord endpoints as (obj<<1|side) */
static int nch;
static long long polyc[4*MAXO+8]; static int OFF;
static long long l1;
static long long cnt, hits;

static inline int P(int code){ int o=code>>1, s=code&1; return s==0? rnk[o]+1 : 2*NOTCH-(rnk[o]+1); }
static inline int encl(int lo,int hi){
  int k=(lo<NOTCH && NOTCH<hi);
  int x0=rnk[0]+1; k+=(lo<x0 && x0<hi);
  int y=P(1<<1|q2side); k+=(lo<y && y<hi);
  for(int i=0;i<nfree;i++) if(fside[i]>=0){ int p=P(fobj[i]<<1|fside[i]); k+=(lo<p&&p<hi);}
  return k;
}
static void addterm(int e,int eps){ long long *c=&polyc[e+OFF]; l1-= llabs(*c); *c+=eps; l1+=llabs(*c); }

static void report(void){
  hits++;
  if(!printhits) return;
  printf("HIT m=%d q2side=%d free:",M,q2side);
  for(int i=0;i<nfree;i++) printf(" (%d,%d)",fside[i],fside[i]>=0?rnk[fobj[i]]:-1);
  printf(" seq:");
  for(int k=0;k<M;k++) printf(" %c%d", cs[k]?'R':'L', rnk[cobj[k]]);
  printf("\n"); fflush(stdout);
}

/* depth = number of crossings placed; cur = departure code of last crossing; e = exponent of last */
static void dfs(int depth,int cur,int e){
  if(depth==M){ cnt++; if(l1==0) report(); return; }
  int rem=M-depth;
  if(getenv("NOPRUNE")==0 && l1>rem) return;
  int last=(depth==M-1);
  int o_new, g_lo, g_hi;
  if(last){ g_lo=g_hi=-1; } else { g_lo=0; g_hi=nobj; }
  for(int g=g_lo; g<=g_hi; g++){
    int sfrom=0, sto=1;
    if(last){ o_new=1; sfrom=sto=1-q2side; }
    else {
      o_new=nobj;
      for(int i=0;i<nobj;i++) if(rnk[i]>=g) rnk[i]++;
      rnk[o_new]=g; nobj++;
    }
    for(int s=sfrom;s<=sto;s++){
      int arr=P(o_new<<1|s), c=P(cur);
      int lo=c<arr?c:arr, hi=c<arr?arr:c;
      int ok=1;
      for(int j=0;j<nch;j++){ int a=P(chA[j]), b=P(chB[j]); if((lo<a&&a<hi)!=(lo<b&&b<hi)){ok=0;break;} }
      if(!ok) continue;
      /* free punctures on sides must not coincide with object positions: they are objects too */
      int k=encl(lo,hi);
      if(k==0) continue;
      int ne=e+(arr<c?k:-k), eps=(s==0)?1:-1;
      addterm(ne,eps);
      chA[nch]=cur; chB[nch]=o_new<<1|s; nch++;
      cobj[depth]=o_new; cs[depth]=s;
      dfs(depth+1, o_new<<1|(1-s), ne);
      nch--;
      addterm(ne,-eps);
    }
    if(!last){
      nobj--;
      for(int i=0;i<nobj;i++) if(rnk[i]>g) rnk[i]--;
    }
  }
}

int main(int argc,char**argv){
  n=atoi(argv[1]); int m0=atoi(argv[2]), m1=atoi(argv[3]); printhits=argc>4;
  nfree=n-3;
  for(M=m0; M<=m1; M++){
    if(M%2) continue;               /* sum eps = algebraic intersection; odd m cannot vanish */
    OFF=2*MAXO; cnt=0; hits=0;
    int ncomb=1; for(int i=0;i<nfree;i++) ncomb*=3;
    for(int c=0;c<ncomb;c++){
      int t=c; int nside=0;
      for(int i=0;i<nfree;i++){ fside[i]=(t%3)-1; t/=3; if(fside[i]>=0) nside++; }
      /* objects: 0 = x0, 1 = q2 (when M>1), then free side punctures; enumerate all rank orders */
      int base = (M>1)?2:1;
      int tot=base+nside;
      int perm[16]; for(int i=0;i<tot;i++) perm[i]=i;
      /* iterate permutations of ranks via Heap-less simple lexicographic next_permutation */
      for(;;){
        nobj=tot; int j=0;
        for(int i=0;i<tot;i++) rnk[i]=perm[i];
        for(int i=0;i<nfree;i++) if(fside[i]>=0) fobj[i]=base+(j++);
        for(int qs=0; qs<=(M>1?1:0); qs++){
          q2side=qs;
          memset(polyc,0,sizeof(polyc)); l1=0; nch=0;
          if(M==1){ /* not used */ }
          cobj[0]=0; cs[0]=0; addterm(0,1);
          dfs(1, 0<<1|1, 0);
          addterm(0,-1);
        }
        /* next permutation */
        int i=tot-2; while(i>=0 && perm[i]>perm[i+1]) i--; if(i<0) break;
        int k=tot-1; while(perm[k]<perm[i]) k--; int tmp=perm[i]; perm[i]=perm[k]; perm[k]=tmp;
        for(int a=i+1,b=tot-1;a<b;a++,b--){tmp=perm[a];perm[a]=perm[b];perm[b]=tmp;}
      }
    }
    printf("n=%d m=%d leaves=%lld hits=%lld\n",n,M,cnt,hits); fflush(stdout);
  }
  return 0;
}
