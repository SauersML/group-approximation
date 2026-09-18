/* Word lower bound for the branched double cover of G=Z^2/<(N1,0),(C,N2)> at {0,g}:
   every finite vertex set U in Z^2 is the mod-2 winding function of a closed lattice loop
   (a word in [F2,F2]) of length Per(U); rank(W-I) = |(1+g) pi(U)|.  So
   max(rank(b-b'),rank(c-c')) >= |(1+g)pi(U)|/Per(U).  Anneal U in a BxB box.
   usage: anneal N1 N2 C g B iters seed  -> prints best ratio, |F|, Per, and U */
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
int N1,N2,C,N,B;
int pimap(int i,int j){ /* element i X + j Y : y=j mod N2 wraps with x-=C */
  int q = (j>=0)? j/N2 : -((-j+N2-1)/N2); int y=j-q*N2; int x=i-q*C; x%=N1; if(x<0)x+=N1; return y*N1+x;}
int main(int argc,char**argv){
  N1=atoi(argv[1]);N2=atoi(argv[2]);C=atoi(argv[3]);int g=atoi(argv[4]);B=atoi(argv[5]);
  long it=atol(argv[6]);srand(atoi(argv[7]));N=N1*N2;
  int gx=g%N1, gy=g/N1; int gel=pimap(gx,gy); /* same as g */
  char *U=calloc(B*B,1),*cnt=calloc(N,1),*bestU=calloc(B*B,1); int *pm=malloc(B*B*sizeof(int));
  int *plusg=malloc(N*sizeof(int)),*minusg=malloc(N*sizeof(int));
  for(int h=0;h<N;h++){int x=h%N1,y=h/N1;plusg[h]=pimap(x+gx,y+gy);} for(int h=0;h<N;h++)minusg[plusg[h]]=h;
  for(int i=0;i<B;i++)for(int j=0;j<B;j++)pm[i*B+j]=pimap(i,j);
  int F=0,P=0; double best=0; int bF=0,bP=0;
  double lam=0.5;
  for(long k=0;k<it;k++){
    if(k%20000==0){ lam = 0.05 + 3.0*((double)rand()/RAND_MAX); }
    int v=rand()%(B*B); int i=v/B,j=v%B;
    /* delta perimeter */
    int nb=0,in=0; int di[4]={1,-1,0,0},dj[4]={0,0,1,-1};
    for(int d=0;d<4;d++){int a=i+di[d],b=j+dj[d]; int inn = (a>=0&&a<B&&b>=0&&b<B)?U[a*B+b]:0; nb++; in+=inn;}
    int dP = U[v]? (2*in-4) : (4-2*in);
    int h=pm[v]; int dF=0;
    /* F(h') = cnt(h') ^ cnt(h'-g). toggling cnt(h) changes F at h and h+g */
    int h1=h,h2=plusg[h];
    if(h1==h2){ } else {
      int f1=cnt[h1]^cnt[minusg[h1]]; int f2=cnt[h2]^cnt[minusg[h2]];
      dF += f1? -1:1; dF += f2? -1:1; }
    int nP=P+dP, nF=F+dF;
    double obj_old=F-lam*P, obj_new=nF-lam*nP;
    double T=0.3;
    if(obj_new>=obj_old || (double)rand()/RAND_MAX < exp((obj_new-obj_old)/T)){
      U[v]^=1; cnt[h]^=1; F=nF; P=nP;
      if(P>0 && (double)F/P>best+1e-9){best=(double)F/P;bF=F;bP=P;for(int q=0;q<B*B;q++)bestU[q]=U[q];}
    }
  }
  printf("%.4f %d %d\n",best,bF,bP);
  if(argc>8){for(int j=B-1;j>=0;j--){for(int i=0;i<B;i++)putchar(bestU[i*B+j]?'#':'.');putchar('\n');}}
  return 0;}
