/* sanov.c -- (ex-sl3z-purely-matricial, 2026-09-13)
   Extreme eigenvalues of the adjacency operator A = a + a^-1 + b + b^-1,
   a = [[1,2],[0,1]], b = [[1,0],[2,1]] (Sanov generators, free of index 12 in SL_2(Z)),
   acting on mean-zero functions:
     mode G: l^2_0(SL_2(F_p))            (Cayley graph, all irreducible sectors)
     mode V: l^2_0(F_p^2 \ {0})          (linear action: principal series + Steinberg sector)
     mode P: l^2_0(P^1(F_p))             (Schreier graph on the projective line: Steinberg sector)
   Ramanujan / Kesten value for F_2 with these generators: 2 sqrt 3 = 3.4641016.
   Method: Lanczos with full reorthogonalization against the constants only, m steps,
   extreme Ritz values by Sturm bisection (Ritz values are inner bounds: lambda_max
   estimates from below, lambda_min from above).
   Usage: ./sanov G|V|P p [m]   (p must be prime) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
static long p; static int64_t *inv;
static inline long md(long x){ x%=p; return x<0?x+p:x; }
static int64_t Ngen[4][4]; /* rows: s = [[s0,s1],[s2,s3]] */
/* mode G: g = (v=(x,y), w = w0(v) + t v), index = (x*p+y-1)*p + t */
static inline void w0(long x,long y,long *u0,long *u1){ if(x){ *u0=0; *u1=inv[x]; } else { *u0=md(-inv[y]); *u1=0; } }
static inline long idxG(long x,long y,long w_0,long w_1){ long a0,a1; w0(x,y,&a0,&a1); long d0=md(w_0-a0), d1=md(w_1-a1); long t = x ? d0*inv[x]%p : d1*inv[y]%p; return (x*p+y-1)*p+t; }
static inline void decG(long i,long *x,long *y,long *w_0,long *w_1){ long t=i%p; long v=i/p+1; *x=v/p; *y=v%p; long a0,a1; w0(*x,*y,&a0,&a1); *w_0=md(a0+t*(*x)); *w_1=md(a1+t*(*y)); }
int main(int argc,char**argv){
  if(argc<3){ fprintf(stderr,"usage\n"); return 1; }
  int modeG = argv[1][0]=='G'; int modeP = argv[1][0]=='P'; int modeV = argv[1][0]=='V'; p=atol(argv[2]); int m = argc>3?atoi(argv[3]):300;
  inv=malloc(p*sizeof(int64_t)); inv[0]=0; for(long i=1;i<p;i++){ long r=1,b=i,e=p-2; while(e){ if(e&1) r=r*b%p; b=b*b%p; e>>=1; } inv[i]=r; }
  long s[4][4]={{1,2,0,1},{1,p-2,0,1},{1,0,2,1},{1,0,p-2,1}}; for(int k=0;k<4;k++) for(int j=0;j<4;j++) Ngen[k][j]=md(s[k][j]);
  long n = modeG ? (p*p-1)*p : (modeP ? p+1 : p*p);
  int32_t *nb = malloc((size_t)n*4*sizeof(int32_t));
  for(long i=0;i<n;i++){
    if(modeG){ long x,y,u0,u1; decG(i,&x,&y,&u0,&u1);
      for(int k=0;k<4;k++){ long X=md(Ngen[k][0]*x+Ngen[k][1]*y), Y=md(Ngen[k][2]*x+Ngen[k][3]*y), W0=md(Ngen[k][0]*u0+Ngen[k][1]*u1), W1=md(Ngen[k][2]*u0+Ngen[k][3]*u1);
        nb[4*i+k]=(int32_t)idxG(X,Y,W0,W1); } }
    else if(modeP){ long z=i; if(z==p){ long h=inv[2]; nb[4*i+0]=(int32_t)p; nb[4*i+1]=(int32_t)p; nb[4*i+2]=(int32_t)h; nb[4*i+3]=(int32_t)(p-h); } else { nb[4*i+0]=(int32_t)((z+2)%p); nb[4*i+1]=(int32_t)((z+p-2)%p); long d1=(2*z+1)%p; nb[4*i+2]= d1? (int32_t)(z*inv[d1]%p) : (int32_t)p; long d2=md(1-2*z); nb[4*i+3]= d2? (int32_t)(z*inv[d2]%p) : (int32_t)p; } }
    else { long x=i/p, y=i%p; for(int k=0;k<4;k++){ long X=md(Ngen[k][0]*x+Ngen[k][1]*y), Y=md(Ngen[k][2]*x+Ngen[k][3]*y); nb[4*i+k]=(int32_t)(X*p+Y); } } }
  /* mask: in mode V exclude index 0 (the zero vector) */
  double *q0=calloc(n,sizeof(double)), *q1=malloc(n*sizeof(double)), *w=malloc(n*sizeof(double));
  double *al=malloc((m+1)*sizeof(double)), *be=malloc((m+1)*sizeof(double));
  uint64_t st=88172645463325252ULL; long cnt = modeV? n-1 : n;
  for(long i=0;i<n;i++){ st^=st<<13; st^=st>>7; st^=st<<17; q1[i]=((st>>11)*(1.0/9007199254740992.0))-0.5; }
  if(modeV) q1[0]=0;
  double mean=0; for(long i=0;i<n;i++) mean+=q1[i]; mean/=cnt; for(long i=0;i<n;i++) q1[i]-=mean; if(modeV) q1[0]=0;
  double nr=0; for(long i=0;i<n;i++) nr+=q1[i]*q1[i]; nr=sqrt(nr); for(long i=0;i<n;i++) q1[i]/=nr;
  double bprev=0; int steps=0;
  for(int j=0;j<m;j++){
    #pragma omp parallel for schedule(static)
    for(long i=0;i<n;i++){ double acc=0; for(int k=0;k<4;k++) acc+=q1[nb[4*i+k]]; w[i]=acc - bprev*q0[i]; }
    if(modeV) w[0]=0;
    double a=0; for(long i=0;i<n;i++) a+=w[i]*q1[i]; for(long i=0;i<n;i++) w[i]-=a*q1[i];
    mean=0; for(long i=0;i<n;i++) mean+=w[i]; mean/=cnt; for(long i=0;i<n;i++) w[i]-=mean; if(modeV) w[0]=0;
    double b=0; for(long i=0;i<n;i++) b+=w[i]*w[i]; b=sqrt(b); al[j]=a; be[j]=b; steps=j+1;
    if(b<1e-12) break; for(long i=0;i<n;i++){ q0[i]=q1[i]; q1[i]=w[i]/b; } bprev=b; }
  /* Sturm count: number of eigenvalues of T < x */
  #define STURM(xx,res) { int cc_=0; double dd_=1; for(int k_=0;k_<steps;k_++){ double off_ = k_? be[k_-1]*be[k_-1] : 0; dd_ = (al[k_]-(xx)) - (k_? off_/dd_ : 0); if(fabs(dd_)<1e-300) dd_=-1e-300; if(dd_<0) cc_++; } res=cc_; }
  double lo=-4.0001, hi=4.0001, xm; int c;
  for(int it=0;it<60;it++){ xm=(lo+hi)/2; STURM(xm,c); if(c>=steps) hi=xm; else lo=xm; } double lmax=(lo+hi)/2;
  lo=-4.0001; hi=4.0001; for(int it=0;it<60;it++){ xm=(lo+hi)/2; STURM(xm,c); if(c>=1) hi=xm; else lo=xm; } double lmin=(lo+hi)/2;
  printf("mode=%s p=%ld dim=%ld lanczos_steps=%d lambda_max=%.6f lambda_min=%.6f norm=%.6f ramanujan=3.464102\n", modeG?"G":(modeP?"P":"V"), p, cnt, steps, lmax, lmin, fabs(lmax)>fabs(lmin)?fabs(lmax):fabs(lmin));
  return 0; }
