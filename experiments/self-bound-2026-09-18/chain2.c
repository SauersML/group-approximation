/* Two-swap chains on square-tiled surfaces (conventions of swap.py).
   Input (stdin): d, then b[0..d-1], then c[0..d-1].  Args: L1 L2 [mode]
   Swap 1: paths P1, P2 with the same move word, length 1..L1; P1 starts at a sector of a cone point, P2 at any
   corner in the same direction (mode 0) -- so P2 may run in a flat donor torus appended to the input.
   Accepted if the 2*L1 sites are distinct and the excess does not go up.
   Swap 2: a slit-pair swap from two sectors of one cone point (same word, length 1..L2) that lowers the excess
   below the starting excess.  Output: the least L1+L2 found (and the least cost at it), or "none".
   Also reports the least single lowering swap (L1 = 0). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define MAXD 2048
int d, B0[MAXD], C0[MAXD];
typedef struct { int b[MAXD], c[MAXD], bi[MAXD], ci[MAXD]; int lab[4*MAXD]; } Surf;
static int uf[4*MAXD];
static int fnd(int x){ while(uf[x]!=x){ uf[x]=uf[uf[x]]; x=uf[x];} return x; }
static void uni(int x,int y){ x=fnd(x); y=fnd(y); if(x!=y) uf[x]=y; }
static void build(Surf*S){ for(int x=0;x<d;x++){ S->bi[S->b[x]]=x; S->ci[S->c[x]]=x; }
  for(int i=0;i<4*d;i++) uf[i]=i;
  for(int x=0;x<d;x++){ uni(4*x+1,4*S->b[x]+0); uni(4*x+2,4*S->b[x]+3); uni(4*x+3,4*S->c[x]+0); uni(4*x+2,4*S->c[x]+1); }
  for(int i=0;i<4*d;i++) S->lab[i]=fnd(i); }
static int excess_bc(const int*b,const int*c){ static int bi[MAXD],ci[MAXD],w[MAXD]; static char seen[MAXD];
  for(int x=0;x<d;x++){ bi[b[x]]=x; ci[c[x]]=x; }
  for(int x=0;x<d;x++) w[x]=b[c[bi[ci[x]]]];
  memset(seen,0,d); int n=0; for(int x=0;x<d;x++) if(!seen[x]){ n++; int y=x; while(!seen[y]){ seen[y]=1; y=w[y]; } }
  return d-n; }
/* state = x*4+k */
static int stepS(const Surf*S,int st,int mv){ int x=st>>2,k=st&3; const int *f,*ni;
  switch(k){ case 0: f=S->b; ni=S->ci; break; case 1: f=S->c; ni=S->b; break; case 2: f=S->bi; ni=S->c; break; default: f=S->ci; ni=S->bi; }
  if(mv==0) return f[x]*4+k; if(mv==1) return x*4+((k+1)&3); return ni[f[x]]*4+((k+3)&3); }
static int siteS(const Surf*S,int st){ int x=st>>2,k=st&3; /* encode: g*MAXD + y, g=0 b, 1 c */
  if(k==0) return MAXD+S->ci[x]; if(k==1) return x; if(k==2) return MAXD+x; return S->bi[x]; }
static int vend(const Surf*S,int st){ return S->lab[4*(st>>2)+(((st&3)+1)&3)]; }
static int nb2,nc2; static int wb[MAXD], wc[MAXD];
/* apply swap of site lists; returns 0 if sites not distinct */
static int apply_swap(const Surf*S,const int*s1,const int*s2,int L,int*b,int*c){
  static int mark[2*MAXD]; static int stamp=0; stamp++;
  for(int i=0;i<L;i++){ if(mark[s1[i]]==stamp) return 0; mark[s1[i]]=stamp; if(mark[s2[i]]==stamp) return 0; mark[s2[i]]=stamp; }
  memcpy(b,S->b,sizeof(int)*d); memcpy(c,S->c,sizeof(int)*d);
  for(int i=0;i<L;i++){ int g=s1[i]>=MAXD, y1=s1[i]%MAXD, y2=s2[i]%MAXD;
    if(!g){ b[y1]=S->b[y2]; b[y2]=S->b[y1]; } else { c[y1]=S->c[y2]; c[y2]=S->c[y1]; } }
  return 1; }
static int rank_diff(const int*f,const int*g){ /* rank(P_f - P_g) = d - #cycles(g^-1 f) */
  static int gi[MAXD],w[MAXD]; static char seen[MAXD];
  for(int x=0;x<d;x++) gi[g[x]]=x; for(int x=0;x<d;x++) w[x]=gi[f[x]];
  memset(seen,0,d); int n=0; for(int x=0;x<d;x++) if(!seen[x]){ n++; int y=x; while(!seen[y]){ seen[y]=1; y=w[y]; } }
  return d-n; }
static int is_cone(const Surf*S,int v){ int n=0; for(int i=0;i<4*d;i++) if(S->lab[i]==v) n++; return n>4; }
/* least lowering swap from pairs of sectors at one cone point; returns L or 0; target: excess < ex_target */
static int best_cost; static int bb2[MAXD], cc2[MAXD];
static int lower_search(const Surf*S,int L2,int ex_target,const int*borig,const int*corig,int*costout){
  static int starts[4*MAXD][2]; int ns=0;
  static int cone[4*MAXD]; static int cnt[4*MAXD]; memset(cnt,0,sizeof(int)*4*d);
  for(int i=0;i<4*d;i++) cnt[S->lab[i]]++;
  for(int i=0;i<4*d;i++) for(int j=i+1;j<4*d;j++) if(S->lab[i]==S->lab[j] && cnt[S->lab[i]]>4 && (i&3)==(j&3)){ starts[ns][0]=i; starts[ns][1]=j; ns++; }
  int P1[64],P2[64],s1[64],s2[64]; static int b[MAXD],c[MAXD];
  for(int L=1;L<=L2;L++){ int found=0, bestc=1<<30;
    long nw=1; for(int i=1;i<L;i++) nw*=3;
    for(int q=0;q<ns;q++) for(long w=0;w<nw;w++){ long ww=w; P1[0]=starts[q][0]; P2[0]=starts[q][1];
        for(int i=1;i<L;i++){ int mv=ww%3; ww/=3; P1[i]=stepS(S,P1[i-1],mv); P2[i]=stepS(S,P2[i-1],mv); }
        if(vend(S,P1[L-1])!=vend(S,P2[L-1])) continue;
        for(int i=0;i<L;i++){ s1[i]=siteS(S,P1[i]); s2[i]=siteS(S,P2[i]); }
        if(!apply_swap(S,s1,s2,L,b,c)) continue;
        if(excess_bc(b,c)<ex_target){ int cb=rank_diff(b,borig), cc=rank_diff(c,corig); int m=cb>cc?cb:cc;
          if(m<bestc){ bestc=m; memcpy(bb2,b,sizeof(int)*d); memcpy(cc2,c,sizeof(int)*d);} found=1; } }
    if(found){ *costout=bestc; return L; } }
  return 0; }
int main(int argc,char**argv){ int L1=atoi(argv[1]), L2=atoi(argv[2]);
  if(scanf("%d",&d)!=1) return 1; for(int i=0;i<d;i++) scanf("%d",&B0[i]); for(int i=0;i<d;i++) scanf("%d",&C0[i]);
  static Surf S, T; memcpy(S.b,B0,sizeof(int)*d); memcpy(S.c,C0,sizeof(int)*d); build(&S);
  int ex0=excess_bc(B0,C0); int cost;
  int L0=lower_search(&S,L2+L1,ex0,B0,C0,&cost);
  printf("excess %d single-swap lowering length %d cost %d\n",ex0,L0,L0?cost:-1);
  int best=1<<30, bestcost=0, bl1=0, bl2=0; static int FB[MAXD],FC[MAXD];
  static int cnt[4*MAXD]; memset(cnt,0,sizeof(cnt)); for(int i=0;i<4*d;i++) cnt[S.lab[i]]++;
  int P1[64],P2[64],s1[64],s2[64];
  for(int L=1;L<=L1;L++){ long nw=1; for(int i=1;i<L;i++) nw*=3;
    for(int a=0;a<4*d;a++){ if(cnt[S.lab[a]]<=4) continue;
      for(int bst=0;bst<4*d;bst++){ if((bst&3)!=(a&3) || bst==a) continue;
        for(long w=0;w<nw;w++){ long ww=w; P1[0]=a; P2[0]=bst;
          for(int i=1;i<L;i++){ int mv=ww%3; ww/=3; P1[i]=stepS(&S,P1[i-1],mv); P2[i]=stepS(&S,P2[i-1],mv); }
          for(int i=0;i<L;i++){ s1[i]=siteS(&S,P1[i]); s2[i]=siteS(&S,P2[i]); }
          if(!apply_swap(&S,s1,s2,L,T.b,T.c)) continue;
          int e1=excess_bc(T.b,T.c); if(e1>ex0) continue;
          if(e1<ex0){ if(L<best){best=L; bestcost=-1; bl1=L; bl2=0; memcpy(FB,T.b,sizeof(int)*d); memcpy(FC,T.c,sizeof(int)*d);} continue; }
          int rem = best - L - 1; if(rem>L2) rem=L2; if(rem<1) continue;
          build(&T); int L2f=lower_search(&T,rem,ex0,B0,C0,&cost);
          if(L2f && L+L2f<best){ best=L+L2f; bestcost=cost; bl1=L; bl2=L2f; memcpy(FB,bb2,sizeof(int)*d); memcpy(FC,cc2,sizeof(int)*d);} } } } }
  if(best<(1<<30)){ printf("two-swap chain: total %d = %d + %d, max-rank cost %d\n",best,bl1,bl2,bestcost);
    if(getenv("PAIR")){ printf("PAIR"); for(int i=0;i<d;i++) printf(" %d",FB[i]); for(int i=0;i<d;i++) printf(" %d",FC[i]); printf("\n"); } }
  else printf("two-swap chain: none (L1<=%d, L2<=%d)\n",L1,L2);
  return 0; }
