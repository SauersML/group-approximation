/* dist.c -- count irreducible representations of G = SL_3(Z/n) that occur in
   C[G/H] for H = Sym^2(SL_2(Z/n) level-d congruence subgroup) (principal SL_2),
   H = block SL_2 (level d), and their union.
   Method: P = permutation character of G on G/H (a class function).  The
   convolution operator f -> P * f on class functions has rank equal to the
   number of irreducible characters chi with <P, chi> != 0.  Its matrix in the
   basis of class indicators, evaluated at class representatives, is
     Q[i][j] = sum_{x in C_j} P(g_i x^{-1}).
   The rank of Q mod two large primes is printed (a lower bound for the rank
   over Q, equal to it unless the primes divide special minors).
   Usage: ./dist n d   (n <= 9 for memory; d | n) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <omp.h>

static int n; static uint64_t NN;
static inline uint32_t enc(const int *m){ uint64_t c=0; for(int i=0;i<9;i++) c=c*n+m[i]; return (uint32_t)c; }
static inline void dec(uint64_t c, int *m){ for(int i=8;i>=0;i--){ m[i]=(int)(c%n); c/=n; } }
static inline void mul(const int *x,const int *y,int *z){
  for(int i=0;i<3;i++) for(int j=0;j<3;j++){ long s=0; for(int k=0;k<3;k++) s+=(long)x[3*i+k]*y[3*k+j]; z[3*i+j]=(int)(s%n); } }
static inline int det3(const int *m){
  long d=(long)m[0]*((long)m[4]*m[8]-(long)m[5]*m[7])-(long)m[1]*((long)m[3]*m[8]-(long)m[5]*m[6])+(long)m[2]*((long)m[3]*m[7]-(long)m[4]*m[6]);
  d%=n; if(d<0)d+=n; return (int)d; }
static inline void inv3(const int *m,int *r){ long t[9];
  t[0]=(long)m[4]*m[8]-(long)m[5]*m[7]; t[1]=-((long)m[1]*m[8]-(long)m[2]*m[7]); t[2]=(long)m[1]*m[5]-(long)m[2]*m[4];
  t[3]=-((long)m[3]*m[8]-(long)m[5]*m[6]); t[4]=(long)m[0]*m[8]-(long)m[2]*m[6]; t[5]=-((long)m[0]*m[5]-(long)m[2]*m[3]);
  t[6]=(long)m[3]*m[7]-(long)m[4]*m[6]; t[7]=-((long)m[0]*m[7]-(long)m[1]*m[6]); t[8]=(long)m[0]*m[4]-(long)m[1]*m[3];
  for(int i=0;i<9;i++){ long v=t[i]%n; if(v<0)v+=n; r[i]=(int)v; } }

static int32_t *cls; static uint32_t *elems; static uint64_t G; static int K;
static uint64_t *csize; static uint32_t *crep;

static int cmpu(const void*a,const void*b){ uint32_t x=*(uint32_t*)a,y=*(uint32_t*)b; return x<y?-1:x>y; }

/* build subgroup list; type 0 = Sym^2, 1 = block; level d */
static uint32_t *build_H(int type,int d,uint64_t *hs){
  uint64_t cap=(uint64_t)n*n*n*n; uint32_t *h=malloc(cap*sizeof(uint32_t)); uint64_t c=0; int m[9];
  for(int a=0;a<n;a++)for(int b=0;b<n;b++)for(int cc=0;cc<n;cc++)for(int dd=0;dd<n;dd++){
    long D=((long)a*dd-(long)b*cc)%n; if(D<0)D+=n; if(D!=1%n) continue;
    if(((a-1)%d)!=0||(b%d)!=0||(cc%d)!=0||((dd-1)%d)!=0) continue;
    if(type==0){ /* columns: images of x^2, xy, y^2 under x->a x + cc y, y-> b x + dd y */
      long v[9]={ (long)a*a, (long)a*b, (long)b*b,
                  2L*a*cc, (long)a*dd+(long)b*cc, 2L*b*dd,
                  (long)cc*cc, (long)cc*dd, (long)dd*dd };
      for(int i=0;i<9;i++){ long w=v[i]%n; if(w<0)w+=n; m[i]=(int)w; }
    } else { int t[9]={a,b,0,cc,dd,0,0,0,1%n}; memcpy(m,t,sizeof t); }
    if(det3(m)!=1%n){ fprintf(stderr,"det fail\n"); exit(1); }
    h[c++]=enc(m); }
  qsort(h,c,sizeof(uint32_t),cmpu); uint64_t u=0; for(uint64_t i=0;i<c;i++) if(i==0||h[i]!=h[i-1]) h[u++]=h[i];
  *hs=u; return h; }

static uint64_t modp(__int128 x,uint64_t p){ long long r=(long long)(x%(__int128)p); if(r<0)r+=p; return (uint64_t)r; }
static int rank_mod(int64_t **Q,int k,uint64_t p){
  uint64_t **A=malloc(k*sizeof(uint64_t*)); for(int i=0;i<k;i++){ A[i]=malloc(k*sizeof(uint64_t)); for(int j=0;j<k;j++) A[i][j]=modp(Q[i][j],p); }
  int r=0; for(int col=0;col<k&&r<k;col++){ int piv=-1; for(int i=r;i<k;i++) if(A[i][col]){piv=i;break;} if(piv<0) continue;
    uint64_t*t=A[piv];A[piv]=A[r];A[r]=t; uint64_t a=A[r][col],inv=1,e=p-2,b=a; while(e){ if(e&1) inv=(unsigned __int128)inv*b%p; b=(unsigned __int128)b*b%p; e>>=1; }
    for(int i=0;i<k;i++) if(i!=r&&A[i][col]){ uint64_t f=(unsigned __int128)A[i][col]*inv%p; for(int j=col;j<k;j++) A[i][j]=(A[i][j]+p-(unsigned __int128)f*A[r][j]%p)%p; }
    r++; }
  for(int i=0;i<k;i++) free(A[i]); free(A); return r; }

/* sum of chi(1)^2 over irreducible chi with <P,chi> = 0, mod p (p > |G|):
   nullspace W of Q spans those chi; project delta_e onto W with the bilinear form
   B(f,g) = sum_j |C_j| f_j g_{j*}; the projection evaluated at e, times |G|, is sum chi(1)^2. */
static uint64_t pw(uint64_t b,uint64_t e,uint64_t p){ uint64_t r=1; while(e){ if(e&1) r=(unsigned __int128)r*b%p; b=(unsigned __int128)b*b%p; e>>=1; } return r; }
static int *invcls; static int eidx;
static long long missing_sq(int64_t **Q,int k,uint64_t p){
  uint64_t **A=malloc(k*sizeof(uint64_t*)); for(int i=0;i<k;i++){ A[i]=malloc(k*sizeof(uint64_t)); for(int j=0;j<k;j++) A[i][j]=modp(Q[i][j],p); }
  int *pivcol=malloc(k*sizeof(int)); int *ispiv=calloc(k,sizeof(int)); int r=0;
  for(int col=0;col<k&&r<k;col++){ int piv=-1; for(int i=r;i<k;i++) if(A[i][col]){piv=i;break;} if(piv<0) continue;
    uint64_t*t=A[piv];A[piv]=A[r];A[r]=t; uint64_t inv=pw(A[r][col],p-2,p); for(int j=0;j<k;j++) A[r][j]=(unsigned __int128)A[r][j]*inv%p;
    for(int i=0;i<k;i++) if(i!=r&&A[i][col]){ uint64_t f=A[i][col]; for(int j=0;j<k;j++) A[i][j]=(A[i][j]+p-(unsigned __int128)f*A[r][j]%p)%p; }
    pivcol[r]=col; ispiv[col]=1; r++; }
  int nd=k-r; if(nd==0){ return 0; }
  uint64_t **b=malloc(nd*sizeof(uint64_t*)); int a=0;
  for(int fc=0;fc<k;fc++) if(!ispiv[fc]){ b[a]=calloc(k,sizeof(uint64_t)); b[a][fc]=1; for(int i=0;i<r;i++) b[a][pivcol[i]]=(p-A[i][fc])%p; a++; }
  uint64_t **M=malloc(nd*sizeof(uint64_t*)); for(int x=0;x<nd;x++){ M[x]=calloc(nd+1,sizeof(uint64_t));
    for(int y=0;y<nd;y++){ unsigned __int128 s=0; for(int j=0;j<k;j++){ s+=(unsigned __int128)(csize[j]%p)*b[x][j]%p*b[y][invcls[j]]%p; s%=p; } M[x][y]=(uint64_t)s; }
    M[x][nd]=b[x][eidx]; }
  for(int col=0,row=0;col<nd;col++){ int piv=-1; for(int i=row;i<nd;i++) if(M[i][col]){piv=i;break;} if(piv<0){ fprintf(stderr,"singular gram\n"); return -1; }
    uint64_t*t=M[piv];M[piv]=M[row];M[row]=t; uint64_t inv=pw(M[row][col],p-2,p); for(int j=0;j<=nd;j++) M[row][j]=(unsigned __int128)M[row][j]*inv%p;
    for(int i=0;i<nd;i++) if(i!=row&&M[i][col]){ uint64_t f=M[i][col]; for(int j=0;j<=nd;j++) M[i][j]=(M[i][j]+p-(unsigned __int128)f*M[row][j]%p)%p; } row++; }
  unsigned __int128 we=0; for(int x=0;x<nd;x++){ we+=(unsigned __int128)M[x][nd]*b[x][eidx]%p; we%=p; }
  uint64_t val=(unsigned __int128)we*(G%p)%p; return (long long)val; }

int main(int argc,char**argv){
  n=atoi(argv[1]); int d=argc>2?atoi(argv[2]):1; NN=1; for(int i=0;i<9;i++) NN*=n;
  cls=malloc(NN*sizeof(int32_t)); memset(cls,0xff,NN*sizeof(int32_t));
  uint64_t cap=0; int m[9];
  for(uint64_t c=0;c<NN;c++){ dec(c,m); if(det3(m)==1%n){ cls[c]=-2; cap++; } }
  G=cap; elems=malloc(G*sizeof(uint32_t)); uint64_t e=0; for(uint64_t c=0;c<NN;c++) if(cls[c]==-2) elems[e++]=(uint32_t)c;
  printf("n=%d d=%d |G|=%lu\n",n,d,(unsigned long)G); fflush(stdout);
  int gen[12][9]; int ng=0; for(int i=0;i<3;i++)for(int j=0;j<3;j++) if(i!=j){ int t[9]={1,0,0,0,1,0,0,0,1}; t[3*i+j]=1; memcpy(gen[ng],t,9*sizeof(int)); inv3(gen[ng],gen[ng+1]); ng+=2; }
  uint32_t *queue=malloc(G*sizeof(uint32_t)); csize=malloc(G*sizeof(uint64_t)); crep=malloc(G*sizeof(uint32_t)); K=0;
  for(uint64_t i=0;i<G;i++){ uint32_t c=elems[i]; if(cls[c]!=-2) continue; cls[c]=K; crep[K]=c; uint64_t qh=0,qt=0; queue[qt++]=c;
    while(qh<qt){ int x[9],y[9],z[9]; dec(queue[qh++],x); for(int g=0;g<ng;g+=2){ mul(gen[g],x,y); mul(y,gen[g+1],z); uint32_t cz=enc(z); if(cls[cz]==-2){ cls[cz]=K; queue[qt++]=cz; } } }
    csize[K]=qt; K++; }
  printf("classes K=%d\n",K); fflush(stdout);
  invcls=malloc(K*sizeof(int)); for(int k=0;k<K;k++){ int x[9],y[9]; dec(crep[k],x); inv3(x,y); invcls[k]=cls[enc(y)]; }
  { int id9[9]={1,0,0,0,1,0,0,0,1}; for(int i=0;i<9;i++) id9[i]%=n; eidx=cls[enc(id9)]; }
  int64_t *P[3]; uint64_t hs[2];
  for(int t=0;t<2;t++){ uint32_t *h=build_H(t,d,&hs[t]); uint64_t *hc=calloc(K,sizeof(uint64_t)); for(uint64_t i=0;i<hs[t];i++) hc[cls[h[i]]]++;
    P[t]=malloc(K*sizeof(int64_t)); for(int k=0;k<K;k++){ __int128 num=(__int128)(G/csize[k])*hc[k]; if(G%csize[k]||num%hs[t]){ fprintf(stderr,"divisibility fail\n"); exit(1);} P[t][k]=(int64_t)(num/hs[t]); }
    int id9[9]={1,0,0,0,1,0,0,0,1}; for(int i=0;i<9;i++) id9[i]%=n;
    printf("H%d size %lu, |G/H|=%ld\n",t,(unsigned long)hs[t],(long)P[t][cls[enc(id9)]]); free(h); free(hc); }
  P[2]=malloc(K*sizeof(int64_t)); for(int k=0;k<K;k++) P[2][k]=P[0][k]+P[1][k];
  for(int t=0;t<3;t++){
    int64_t **Q=malloc(K*sizeof(int64_t*)); for(int i=0;i<K;i++) Q[i]=calloc(K,sizeof(int64_t));
    #pragma omp parallel for schedule(dynamic)
    for(int i=0;i<K;i++){ int gi[9]; dec(crep[i],gi); int64_t *row=Q[i];
      for(uint64_t x=0;x<G;x++){ int xm[9],xi[9],y[9]; dec(elems[x],xm); inv3(xm,xi); mul(gi,xi,y); row[cls[elems[x]]]+=P[t][cls[enc(y)]]; } }
    int r1=rank_mod(Q,K,2305843009213693951ULL), r2=rank_mod(Q,K,1000000007ULL);
    long long ms=missing_sq(Q,K,2305843009213693951ULL);
    printf("type %s: irreps occurring (rank mod p1, p2) = %d, %d of K=%d; sum of dim^2 over missing irreps = %lld\n", t==0?"Sym2":(t==1?"block":"union"), r1, r2, K, ms); fflush(stdout);
    for(int i=0;i<K;i++) free(Q[i]); free(Q); }
  printf("DONE\n"); return 0; }
