/* chisec.c -- (ex-sl3z-purely-matricial, 2026-09-13)
   Per-sector extreme eigenvalues of A = a + a^-1 + b + b^-1 (Sanov generators
   a = [[1,2],[0,1]], b = [[1,0],[2,1]]) on the principal series Ind_B^{SL_2(F_p)}(chi),
   realised on P^1(F_p) with representatives v_z = (z,1), v_inf = (1,0):
     (A f)(z) = sum_s chi(t_s(z)) f(s.z),   s v_z = t_s(z) v_{s.z}.
   chi(g^j) = exp(2 pi i j k/(p-1)) for a primitive root g.  k = 0 is 1 + Steinberg (constants removed).
   Lanczos (m steps, no reorthogonalization), extreme Ritz values by Sturm bisection.
   Prints the sectors with the largest norms.  Usage: ./chisec p [m] [top] */
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <complex.h>
#include <stdint.h>
static long p;
static long pw(long b,long e){ long r=1; b%=p; while(e){ if(e&1) r=r*b%p; b=b*b%p; e>>=1; } return r; }
typedef struct { int k; int order; double lmax, lmin, norm; } res_t;
static int cmpr(const void*a,const void*b){ double x=((res_t*)a)->norm, y=((res_t*)b)->norm; return x<y?1:(x>y?-1:0); }
static long gcdl(long a,long b){ while(b){ long t=a%b; a=b; b=t; } return a; }
int main(int argc,char**argv){
  p=atol(argv[1]); int m=argc>2?atoi(argv[2]):250; int top=argc>3?atoi(argv[3]):12;
  long n=p+1, g=2;
  for(;;g++){ int ok=1; long q=p-1; for(long f=2; f*f<=q; f++) if(q%f==0){ if(pw(g,(p-1)/f)==1){ok=0;break;} while(q%f==0) q/=f; } if(ok && q>1 && pw(g,(p-1)/q)==1) ok=0; if(ok) break; }
  long *dlog=malloc(p*sizeof(long)); long x=1; for(long j=0;j<p-1;j++){ dlog[x]=j; x=x*g%p; }
  long s[4][4]={{1,2,0,1},{1,p-2,0,1},{1,0,2,1},{1,0,p-2,1}};
  int32_t *img=malloc(4*n*sizeof(int32_t)); int32_t *lg=malloc(4*n*sizeof(int32_t));
  for(long z=0;z<n;z++){ long v0 = (z==p)?1:z, v1=(z==p)?0:1;
    for(int k=0;k<4;k++){ long X=(s[k][0]*v0+s[k][1]*v1)%p, Y=(s[k][2]*v0+s[k][3]*v1)%p;
      if(Y){ long iy=pw(Y,p-2); img[4*z+k]=(int32_t)(X*iy%p); lg[4*z+k]=(int32_t)dlog[Y]; }
      else { img[4*z+k]=(int32_t)p; lg[4*z+k]=(int32_t)dlog[X]; } } }
  res_t *R=malloc((p-1)*sizeof(res_t));
  #pragma omp parallel for schedule(dynamic)
  for(long kk=0; kk<p-1; kk++){
    double complex *ph=malloc(4*n*sizeof(double complex));
    for(long i=0;i<4*n;i++) ph[i]=cexp(2*M_PI*I*(double)lg[i]*(double)kk/(double)(p-1));
    double complex *q0=calloc(n,sizeof(double complex)), *q1=malloc(n*sizeof(double complex)), *w=malloc(n*sizeof(double complex));
    double *al=malloc(m*sizeof(double)), *be=malloc(m*sizeof(double));
    uint64_t st=88172645463325252ULL ^ (uint64_t)(kk*2654435761u);
    for(long i=0;i<n;i++){ st^=st<<13; st^=st>>7; st^=st<<17; double re=((st>>11)*(1.0/9007199254740992.0))-0.5; st^=st<<13; st^=st>>7; st^=st<<17; double im=((st>>11)*(1.0/9007199254740992.0))-0.5; q1[i]=re+I*im; }
    if(kk==0){ double complex mu=0; for(long i=0;i<n;i++) mu+=q1[i]; mu/=n; for(long i=0;i<n;i++) q1[i]-=mu; }
    double nr=0; for(long i=0;i<n;i++) nr+=creal(q1[i]*conj(q1[i])); nr=sqrt(nr); for(long i=0;i<n;i++) q1[i]/=nr;
    double bprev=0; int steps=0;
    for(int j=0;j<m;j++){
      for(long i=0;i<n;i++){ double complex acc=0; for(int k=0;k<4;k++) acc+=ph[4*i+k]*q1[img[4*i+k]]; w[i]=acc-bprev*q0[i]; }
      double a=0; for(long i=0;i<n;i++) a+=creal(conj(q1[i])*w[i]); for(long i=0;i<n;i++) w[i]-=a*q1[i];
      if(kk==0){ double complex mu=0; for(long i=0;i<n;i++) mu+=w[i]; mu/=n; for(long i=0;i<n;i++) w[i]-=mu; }
      double b=0; for(long i=0;i<n;i++) b+=creal(w[i]*conj(w[i])); b=sqrt(b); al[j]=a; be[j]=b; steps=j+1;
      if(b<1e-12) break; for(long i=0;i<n;i++){ q0[i]=q1[i]; q1[i]=w[i]/b; } bprev=b; }
    double lo=-4.0001,hi=4.0001,lmax,lmin;
    for(int it=0;it<55;it++){ double xm=(lo+hi)/2; int cc=0; double dd=1; for(int t=0;t<steps;t++){ dd=(al[t]-xm)-(t? be[t-1]*be[t-1]/dd:0); if(fabs(dd)<1e-300) dd=-1e-300; if(dd<0) cc++; } if(cc>=steps) hi=xm; else lo=xm; } lmax=(lo+hi)/2;
    lo=-4.0001; hi=4.0001;
    for(int it=0;it<55;it++){ double xm=(lo+hi)/2; int cc=0; double dd=1; for(int t=0;t<steps;t++){ dd=(al[t]-xm)-(t? be[t-1]*be[t-1]/dd:0); if(fabs(dd)<1e-300) dd=-1e-300; if(dd<0) cc++; } if(cc>=1) hi=xm; else lo=xm; } lmin=(lo+hi)/2;
    R[kk].k=(int)kk; R[kk].order=(int)((p-1)/gcdl(kk,p-1)); R[kk].lmax=lmax; R[kk].lmin=lmin; R[kk].norm=fabs(lmax)>fabs(lmin)?fabs(lmax):fabs(lmin);
    free(ph); free(q0); free(q1); free(w); free(al); free(be); }
  printf("p=%ld primitive_root=%ld sectors=%ld steps=%d  (2 sqrt 3 = 3.464102)\n", p, g, p-1, m);
  printf("k=0 (Steinberg): lmax=%.6f lmin=%.6f\n", R[0].lmax, R[0].lmin);
  printf("k=(p-1)/2 (quadratic): lmax=%.6f lmin=%.6f\n", R[(p-1)/2].lmax, R[(p-1)/2].lmin);
  qsort(R,p-1,sizeof(res_t),cmpr);
  for(int i=0;i<top && i<p-1;i++) printf("rank %d: k=%d order=%d lmax=%.6f lmin=%.6f norm=%.6f\n", i+1, R[i].k, R[i].order, R[i].lmax, R[i].lmin, R[i].norm);
  int above=0; for(long i=0;i<p-1;i++) if(R[i].norm>3.4641016+0.01) above++;
  printf("sectors with norm > 2sqrt3 + 0.01: %d of %ld\nDONE\n", above, p-1);
  return 0; }
