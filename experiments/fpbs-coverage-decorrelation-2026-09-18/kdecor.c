/* Coverage decorrelation constant K(S,k) = q(S)/(q(S_<k) q(S_>k)) for the
 * percolation spine on a straight Z^2 path, where q(F) = P(every run of F is
 * attached | F forced open).  Spine proxy: open edges whose endpoint is joined
 * to the boundary of a box with margin M around the path (M >> xi gives the
 * supercritical spine; p'=1/2 and finite M gives the critical proxy).
 *
 * usage: kdecor p M n samples seed
 * Path: x_i = (M+i, M), i=0..n, edges e_1..e_n; split edge k = n/2.
 * Patterns (all exclude e_k):
 *   full   : all edges
 *   alt    : odd-indexed edges
 *   sparse4: edges i = 1 mod 4
 *   rand1..3: fixed random subsets of density 1/2
 * Output per pattern: q(S), q(A), q(B), K = q(S)/(q(A)q(B)), K*theta, with
 * batch-jackknife standard errors (20 batches).
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

#define NP 6
#define NB 20
static const char *pname[NP]={"full","alt","sparse4","rand1","rand2","rand3"};

int n,k;
int root[200];      /* off-path root of path vertex i */
int att[200];       /* root is boundary */
int pe[200];        /* random state of path edge e_i (1..n) */

/* small UF on path vertices */
static int sp[200];
static int sf(int x){while(sp[x]!=x){sp[x]=sp[sp[x]];x=sp[x];}return x;}
static void su(int a,int b){a=sf(a);b=sf(b);if(a!=b)sp[a]=b;}

/* forced set F (bitmask array f[1..n]); returns 1 if every run of F attached */
static int event(const int *f){
  int i,j; int satt[200];
  for(i=0;i<=n;i++)sp[i]=i;
  for(i=1;i<=n;i++) if(f[i]||pe[i]) su(i-1,i);
  for(i=0;i<=n;i++)for(j=i+1;j<=n;j++) if(root[i]==root[j]) su(i,j);
  for(i=0;i<=n;i++)satt[i]=0;
  for(i=0;i<=n;i++) if(att[i]) satt[sf(i)]=1;
  for(i=1;i<=n;i++) if(f[i]){ if(!satt[sf(i)]) return 0; }
  return 1;
}

int main(int argc,char**argv){
  if(argc<6){fprintf(stderr,"usage\n");return 1;}
  double p=atof(argv[1]); int M=atoi(argv[2]); n=atoi(argv[3]); long S=atol(argv[4]);
  s[0]=0x9E3779B97F4A7C15ULL^atol(argv[5]); s[1]=0xD1B54A32D192ED03ULL+atol(argv[5])*7919; for(int i=0;i<20;i++)nxt();
  k=n/2;
  int W=n+2*M+1, H=2*M+1, NV=W*H, BND=NV;
  par=malloc(sizeof(int)*(NV+1));
  int f[NP][3][200]; memset(f,0,sizeof f);
  uint64_t save0=s[0],save1=s[1]; s[0]=12345; s[1]=67890;
  for(int t=0;t<NP;t++) for(int i=1;i<=n;i++){
    int in=0;
    if(t==0) in=1; else if(t==1) in=(i%2==1); else if(t==2) in=(i%4==1); else in=(unif()<0.5);
    if(i==k) in=0;
    f[t][0][i]=in; if(i<k) f[t][1][i]=in; if(i>k) f[t][2][i]=in;
  }
  s[0]=save0; s[1]=save1;
  double cnt[NB][NP][3]; double th[NB]; memset(cnt,0,sizeof cnt); memset(th,0,sizeof th);
  for(long sm=0;sm<S;sm++){
    int b=sm%NB;
    for(int v=0;v<=NV;v++)par[v]=v;
    for(int y=0;y<H;y++)for(int x=0;x<W;x++){
      int v=y*W+x;
      if(x==0||y==0||x==W-1||y==H-1) uni(v,BND);
      if(x+1<W){ int onpath=(y==M && x>=M && x<M+n);
        if(onpath) pe[x-M+1]=(unif()<p);
        else if(unif()<p) uni(v,v+1); }
      if(y+1<H){ if(unif()<p) uni(v,v+W); }
    }
    int rb=fnd(BND);
    for(int i=0;i<=n;i++){ root[i]=fnd(M*W+M+i); att[i]=(root[i]==rb); }
    /* theta proxy at middle vertex, path edges random */
    { int z[200]; memset(z,0,sizeof z);
      for(int i=0;i<=n;i++)sp[i]=i;
      for(int i=1;i<=n;i++) if(pe[i]) su(i-1,i);
      for(int i=0;i<=n;i++)for(int j=i+1;j<=n;j++) if(root[i]==root[j]) su(i,j);
      int a=0; for(int i=0;i<=n;i++) if(att[i]&&sf(i)==sf(k)) a=1;
      th[b]+=a; (void)z; }
    for(int t=0;t<NP;t++)for(int c=0;c<3;c++) cnt[b][t][c]+=event(f[t][c]);
  }
  double per=(double)S/NB;
  double thT=0; for(int b=0;b<NB;b++)thT+=th[b]; thT/=S;
  printf("# p=%g M=%d n=%d k=%d samples=%ld theta_proxy=%.4f\n",p,M,n,k,S,thT);
  printf("# pattern |S| qS qA qB K K*theta K_se Ktheta_se\n");
  for(int t=0;t<NP;t++){
    double T[3]={0,0,0}; for(int b=0;b<NB;b++)for(int c=0;c<3;c++)T[c]+=cnt[b][t][c];
    double q[3]; for(int c=0;c<3;c++) q[c]=T[c]/S;
    double K=q[0]/(q[1]*q[2]), KT=K*thT;
    /* jackknife */
    double js=0,js2=0,jt=0,jt2=0;
    for(int b=0;b<NB;b++){
      double qq[3]; for(int c=0;c<3;c++) qq[c]=(T[c]-cnt[b][t][c])/(S-per);
      double tb=(thT*S-th[b])/(S-per);
      double Kb=qq[0]/(qq[1]*qq[2]); js+=Kb; js2+=Kb*Kb; jt+=Kb*tb; jt2+=Kb*tb*Kb*tb;
    }
    js/=NB; js2/=NB; jt/=NB; jt2/=NB;
    double se=sqrt((NB-1)*(js2-js*js)), set=sqrt((NB-1)*(jt2-jt*jt));
    int sz=0; for(int i=1;i<=n;i++) sz+=f[t][0][i];
    printf("%-8s %3d %.5f %.5f %.5f %.4f %.4f %.4f %.4f\n",pname[t],sz,q[0],q[1],q[2],K,KT,se,set);
  }
  return 0;
}
