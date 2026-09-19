/* w22-123 margin.c: extends w21-123 wind.c (unchanged sampler and lift) with the margin
 * statistics of the rotated slit events.  Per sample on E0 it records the bad set B (720 bins)
 * and computes rho = distance from a good angle to B, E[rho;U^Phi], the two-angle function
 * h(s) = P(U^phi & U^{phi+s}) at a list of shifts s, and a surrogate in which every wide
 * component's bad arc gets an independent uniform offset (lengths kept), R=8 copies.
 * Original header of wind.c follows.
 * w21-123: winding characterization of the half-plane slit events U_n, L_n, D'_n(0).
 * Conventions of karm.c (w19-123): triangular site percolation p=1/2, axial (i,j),
 * x=i+j/2, y=j*sqrt(3)/2, B_n={|j|<=n,|2i+j|<=2n}, boundary black (wired), I_n = black
 * cluster of the boundary, S_n={(i,0):-n<i<=0}, P_n={(i,0):i>=1}.  A white step x->y is
 * pinched if both common neighbours of x,y are in I_n.  z0=(1/2,0) is the slit point.
 *  U (L): no pinch-free white path inside {j>=0} ({j<=0}) from S_n to P_n (direct BFS).
 *  E0 = {0 in I} or {(1,0) in I} or {(0,1),(1,-1) in I}.
 *  On E0, every pinch-free white component W carries a lifted argument about z0 (checked:
 *  column 'wind'), with range [m_W,M_W], length l_W.  Theorem A predicts
 *  U = E0 & no W with [2k pi,(2k+1)pi] in [m_W,M_W];  L = same with [(2k-1)pi,2k pi].
 *  Wt = E0 & all l_W < t (t = pi, 2pi, 3pi).
 *  g_U = fraction of rotations phi in [0,2pi) for which no W has [2k pi+phi,(2k+1)pi+phi]
 *  inside its range (720 bins); g_UL = fraction good for both phi and phi+pi.
 * usage: wind n samples seed */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>
static uint64_t s[2];
static uint64_t nx(void){uint64_t a=s[0],b=s[1];s[0]=b;a^=a<<23;s[1]=a^b^(a>>17)^(b>>26);return s[1]+b;}
static int N,Wd; static unsigned char *col; static int *mark,*vis,*q; static int stamp=0; static double *lift;
#define ID(i,j) (((j)+N)*Wd+((i)+2*N))
static const int d[6][2]={{1,0},{0,1},{-1,1},{-1,0},{0,-1},{1,-1}};
static int inbox(int i,int j,int n){ if(j<-n||j>n) return 0; int x2=2*i+j; return x2>=-2*n&&x2<=2*n; }
static int isbd(int i,int j,int n){ if(!inbox(i,j,n)) return 0;
  for(int k=0;k<6;k++) if(!inbox(i+d[k][0],j+d[k][1],n)) return 1; return 0; }
static int st;
static int isI(int i,int j,int n){ return inbox(i,j,n) && mark[ID(i,j)]==st; }
static void cluster(int n){ st=++stamp; int h=0,tl=0;
  for(int j=-n;j<=n;j++) for(int i=-2*n;i<=2*n;i++) if(isbd(i,j,n)){int id=ID(i,j); mark[id]=st; q[tl++]=id;}
  while(h<tl){ int id=q[h++]; int j=id/Wd-N,i=id%Wd-2*N;
    for(int k=0;k<6;k++){int a=i+d[k][0],b=j+d[k][1]; if(!inbox(a,b,n))continue; int e=ID(a,b);
      if(mark[e]==st||!col[e])continue; mark[e]=st;q[tl++]=e;} } }
static int pinched(int i,int j,int k,int n){ int k1=(k+5)%6,k2=(k+1)%6;
  return isI(i+d[k1][0],j+d[k1][1],n)&&isI(i+d[k2][0],j+d[k2][1],n); }
static int half(int side,int n){ int hs=++stamp,h=0,tl=0;
  for(int i=-n+1;i<=0;i++){ int id=ID(i,0); if(mark[id]!=st){ vis[id]=hs; q[tl++]=id; } }
  while(h<tl){ int id=q[h++]; int j=id/Wd-N,i=id%Wd-2*N; if(j==0&&i>=1) return 0;
    for(int k=0;k<6;k++){ int a=i+d[k][0],b=j+d[k][1]; if(!inbox(a,b,n)||side*b<0) continue; int e=ID(a,b);
      if(mark[e]==st||vis[e]==hs) continue; if(pinched(i,j,k,n)) continue; vis[e]=hs; q[tl++]=e; } }
  return 1; }
static double argz(int i,int j){ return atan2(j*0.8660254037844386, i+0.5*j-0.5); }
#define NB 720
static unsigned char badU[NB], badR[NB];
#define MAXA 4096
static double am[MAXA], al[MAXA]; static int na;
static const int SH[12]={0,1,2,4,8,16,32,64,120,180,270,360};
static double sh[12], sR[3], srho, srhoR, sna, sna2, slen;
static void markbad2(unsigned char*bb,double m,double len){ if(len<0) return; if(len>=2*M_PI){ for(int b=0;b<NB;b++) bb[b]=1; return; }
  for(int b=0;b<NB;b++){ double phi=(b+0.5)*2*M_PI/NB; double t=fmod(phi-m,2*M_PI); if(t<0)t+=2*M_PI; if(t<=len) bb[b]=1; } }
static double rhosum(unsigned char*bb){ /* sum over good bins of distance (radians) to nearest bad bin, /NB */
  int any=0; for(int b=0;b<NB;b++) any|=bb[b]; if(!any) return M_PI;
  static int dl[NB]; int last=-100000; for(int r=0;r<2;r++) for(int b=0;b<NB;b++){ int t=r*NB+b; if(bb[b]) last=t; if(r) dl[b]=t-last; }
  double s=0; int nxt=100000; for(int r=1;r>=0;r--) for(int b=NB-1;b>=0;b--){ int t=r*NB+b; if(bb[b]) nxt=t; if(!r){ int dd=nxt-t; if(dl[b]<dd) dd=dl[b]; if(!bb[b]) s+=(dd-0.5)*2*M_PI/NB; } }
  return s/NB; }
static void markbad(double m,double M){ /* phi bad iff exists k: m<=phi+2k pi and phi+2k pi+pi<=M */
  double len=M-m-M_PI; if(len<0) return; if(len>=2*M_PI){ for(int b=0;b<NB;b++) badU[b]=1; return; }
  for(int b=0;b<NB;b++){ double phi=(b+0.5)*2*M_PI/NB; double t=fmod(phi-m,2*M_PI); if(t<0)t+=2*M_PI;
    if(t<=len) badU[b]=1; } }
static int cellin(double m,double M,double off){ /* exists k: m<=off+2k pi and off+2k pi+pi<=M */
  double e=1e-9; double k=ceil((m-off-e)/(2*M_PI)); return off+2*M_PI*k+M_PI<=M+e; }
int main(int argc,char**argv){
  int n=atoi(argv[1]); long long T=atoll(argv[2]); N=n; Wd=4*N+1; int H=2*N+1;
  col=calloc(Wd*H,1); mark=calloc(Wd*H,sizeof(int)); vis=calloc(Wd*H,sizeof(int)); q=malloc(sizeof(int)*Wd*H*2);
  lift=malloc(sizeof(double)*Wd*H);
  s[0]=atoll(argv[3])*0x9E3779B97F4A7C15ULL+1; s[1]=0xdeadbeef^s[0]; for(int k=0;k<20;k++)nx();
  long long cC=0,cE=0,cU=0,cL=0,cD=0,cW1=0,cW2=0,cW3=0,vU=0,vL=0,vE=0,vw=0; double sgU=0,sgUL=0,sgU2=0;
  for(long long z=0;z<T;z++){
    for(int j=-n;j<=n;j++) for(int i=-2*n;i<=2*n;i++) if(inbox(i,j,n)) col[ID(i,j)]= isbd(i,j,n)?1:(nx()>>63)&1;
    cluster(n);
    int C=isI(0,0,n), E0=C||isI(1,0,n)||(isI(0,1,n)&&isI(1,-1,n));
    int U=half(1,n), L=half(-1,n);
    cC+=C; cE+=E0; cU+=U; cL+=L; cD+=U&&L; if((U||L)&&!E0) vE++;
    if(!E0) continue;
    int vs=++stamp, Uc=1, Lc=1; double lmax=0; na=0; for(int b=0;b<NB;b++) badU[b]=0;
    for(int j=-n;j<=n;j++) for(int i=-2*n;i<=2*n;i++){ if(!inbox(i,j,n)) continue; int id=ID(i,j);
      if(mark[id]==st||vis[id]==vs) continue;
      int h=0,tl=0; vis[id]=vs; lift[id]=argz(i,j); q[tl++]=id; double m=lift[id],M=m;
      while(h<tl){ int c=q[h++]; int cj=c/Wd-N,ci=c%Wd-2*N; double ac=argz(ci,cj);
        for(int k=0;k<6;k++){ int a=ci+d[k][0],b=cj+d[k][1]; if(!inbox(a,b,n)) continue; int e=ID(a,b);
          if(mark[e]==st||pinched(ci,cj,k,n)) continue;
          double df=argz(a,b)-ac; if(df>M_PI) df-=2*M_PI; if(df<-M_PI) df+=2*M_PI; double cand=lift[c]+df;
          if(vis[e]==vs){ if(fabs(lift[e]-cand)>1e-7) vw++; continue; }
          vis[e]=vs; lift[e]=cand; q[tl++]=e; if(cand<m)m=cand; if(cand>M)M=cand; } }
      if(cellin(m,M,0)) Uc=0; if(cellin(m,M,-M_PI)) Lc=0; if(M-m>lmax) lmax=M-m; markbad(m,M); if(M-m>=M_PI&&na<MAXA){ am[na]=m; al[na]=M-m-M_PI; na++; } }
    if(Uc!=U) vU++; if(Lc!=L) vL++;
    cW1+=lmax<M_PI; cW2+=lmax<2*M_PI; cW3+=lmax<3*M_PI;
    int gu=0,gul=0; for(int b=0;b<NB;b++){ if(!badU[b]){ gu++; if(!badU[(b+NB/2)%NB]) gul++; } }
    srho+=rhosum(badU); sna+=na; sna2+=(double)na*na; for(int a=0;a<na;a++) slen+=al[a];
    for(int k=0;k<12;k++){ int c=0; for(int b=0;b<NB;b++) c+=!badU[b]&&!badU[(b+SH[k])%NB]; sh[k]+=(double)c/NB; }
    for(int r=0;r<8;r++){ for(int b=0;b<NB;b++) badR[b]=0;
      for(int a=0;a<na;a++) markbad2(badR,(nx()>>11)*(2*M_PI/9007199254740992.0),al[a]);
      int g1=0,g2=0; for(int b=0;b<NB;b++) if(!badR[b]){ g1++; if(!badR[(b+NB/2)%NB]) g2++; }
      sR[0]+=g1/(8.0*NB); sR[1]+=g2/(8.0*NB); sR[2]+=(double)g1*g1/(8.0*NB*NB); srhoR+=rhosum(badR)/8; }
    sgU+=(double)gu/NB; sgUL+=(double)gul/NB; sgU2+=(double)gu*gu/((double)NB*NB);
  }
  double t=(double)T;
  printf("n=%d T=%lld C=%.5f E0=%.5f U=%.5f L=%.5f D=%.5f Wpi=%.5f W2pi=%.5f W3pi=%.5f gU=%.5f gUL=%.5f gU2=%.5f\n",
    n,T,cC/t,cE/t,cU/t,cL/t,cD/t,cW1/t,cW2/t,cW3/t,sgU/t,sgUL/t,sgU2/t);
  printf("margin n=%d Erho1U=%.6f Na1E0=%.5f Na2=%.5f sumlen1E0=%.5f h:",n,srho/t,sna/t,sna2/t,slen/t); for(int k=0;k<12;k++) printf(" %d:%.5f",SH[k],sh[k]/t);
  printf("\nsurrogate n=%d gU=%.5f gUL=%.5f gU2=%.5f Erho1U=%.6f\n",n,sR[0]/t,sR[1]/t,sR[2]/t,srhoR/t);
  printf("violations: U/L without E0 %lld  wind %lld  U!=Uchar %lld  L!=Lchar %lld\n",vE,vw,vU,vL);
  return 0; }
