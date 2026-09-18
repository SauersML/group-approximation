/* Exact counting of star-stage exploration outcomes for the multitype GW lower bound on theta(p)
   on Cay(F_2 x Z, S_rig), S_rig = {(a,0),(a,1),(a,3),(b,0),(b,1),(b,4),(1,1)}^{+-}.
   Row type (s,G): fibre entered by letter s, entry height set G (bit0 set, span<W, |G|<=K).
   Stage explores: vertical edges of the fibre (heights in [-A, W-1+A]), ladder edges to the three
   child fibres t != s^-1, and back ladder edges from discovered child vertices. Exploration stops
   when p^i q^j < eps (i open, j closed revealed edges). Output: counts[childtype][i][j].
   Child type (t, cap(C_t)): cap keeps heights < min+W, then the K smallest. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>
#include <string.h>
int W,K,A; double logeps, lp, lq;
int D[4][3];
#define OFF 32
#define IMAX 16
#define JMAX 256
int ntypes; int *tid; /* bitset (W bits) -> id or -1 */
uint64_t *cnt; /* [4*ntypes][IMAX][JMAX] */
typedef struct { uint64_t P; uint64_t C[4]; int8_t qk[96]; int8_t qh[96]; int qlen; } St;
int kids[3]; int nk;
static inline int pwin(int h){ return h>=-A && h<=W-1+A; }
void leaf(const St*s,int i,int j){
  for(int k=0;k<nk;k++){ int t=kids[k]; uint64_t b=s->C[t]; if(!b) continue;
    int m=__builtin_ctzll(b); uint64_t x=b>>m; if(W<64) x&=((1ULL<<W)-1);
    uint64_t y=0; int c=0; while(x && c<K){ uint64_t low=x&(-x); y|=low; x^=low; c++; }
    int id=tid[y]; if(id<0){fprintf(stderr,"bad type\n");exit(1);}
    cnt[((uint64_t)(t*ntypes+id)*IMAX+i)*JMAX+j]++; }
}
void explore(St s,int qpos,int e,int i,int j){
  for(;;){
    if(i*lp+j*lq<logeps){ leaf(&s,i,j); return; }
    if(qpos>=s.qlen){ leaf(&s,i,j); return; }
    int kind=s.qk[qpos], h=s.qh[qpos];
    /* enumerate edge e of current vertex: target */
    int tk=-2, th=0;
    if(kind<0){ /* P vertex: edges 0,1 vertical; then 3 kids x 3 d */
      int ne=2+3*nk; if(e>=ne){qpos++;e=0;continue;}
      if(e<2){ tk=-1; th = e==0? h-1 : h+1; if(!pwin(th) || (s.P>>(th+OFF)&1)){e++;continue;} }
      else { int k=(e-2)/3, d=(e-2)%3; tk=kids[k]; th=h+D[tk][d]; if(s.C[tk]>>(th+OFF)&1){e++;continue;} }
    } else { int t=kind; if(e>=3){qpos++;e=0;continue;}
      tk=-1; th=h-D[t][e]; if(!pwin(th) || (s.P>>(th+OFF)&1)){e++;continue;} }
    if(j+1<JMAX) explore(s,qpos,e+1,i,j+1); /* closed */
    else { leaf(&s,i,j); }
    /* open */
    if(tk<0) s.P|=1ULL<<(th+OFF); else s.C[tk]|=1ULL<<(th+OFF);
    if(s.qlen>=96||i+1>=IMAX){ leaf(&s,i+1,j); return; }
    s.qk[s.qlen]=tk; s.qh[s.qlen]=th; s.qlen++;
    i++; e++;
  }
}
int main(int argc,char**argv){
  int pn=atoi(argv[1]), pd=atoi(argv[2]); { int z0=atoi(argv[7]), w0=atoi(argv[8]); int T[4][3]={{0,1,z0},{0,-1,-z0},{0,1,w0},{0,-1,-w0}}; memcpy(D,T,sizeof T); } W=atoi(argv[3]); K=atoi(argv[4]); A=atoi(argv[5]); double eps=atof(argv[6]);
  double p=(double)pn/pd; lp=log(p); lq=log(1-p); logeps=log(eps);
  tid=malloc(sizeof(int)<<W); for(int x=0;x<(1<<W);x++) tid[x]=-1;
  int *tbits=malloc(sizeof(int)<<W); ntypes=0;
  for(int x=1;x<(1<<W);x+=2) if(__builtin_popcount(x)<=K){ tid[x]=ntypes; tbits[ntypes++]=x; }
  cnt=calloc((size_t)4*ntypes*IMAX*JMAX,8);
  printf("W %d K %d A %d eps %g p %d/%d ntypes %d\n",W,K,A,eps,pn,pd,ntypes);
  for(int s=0;s<4;s++) for(int g=0;g<ntypes;g++){
    memset(cnt,0,(size_t)4*ntypes*IMAX*JMAX*8);
    nk=0; for(int t=0;t<4;t++) if(t!=(s^1)) kids[nk++]=t;
    St st; memset(&st,0,sizeof st);
    for(int h=0;h<W;h++) if(tbits[g]>>h&1){ st.P|=1ULL<<(h+OFF); st.qk[st.qlen]=-1; st.qh[st.qlen]=h; st.qlen++; }
    explore(st,0,0,0,0);
    for(uint64_t c=0;c<(uint64_t)4*ntypes;c++) for(int i=0;i<IMAX;i++) for(int j=0;j<JMAX;j++){
      uint64_t v=cnt[(c*IMAX+i)*JMAX+j]; if(v) printf("R %d %d C %llu %d %d %d %llu\n",s,tbits[g],(unsigned long long)(c/ntypes),tbits[c%ntypes],i,j,(unsigned long long)v);
    }
  }
}
