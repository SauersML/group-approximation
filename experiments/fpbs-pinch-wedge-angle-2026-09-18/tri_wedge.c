/* Triangular-lattice analogue of the box event D_n (site percolation, p=1/2).
 * Axial coords (i,j): position x = i + j/2, y = j*sqrt(3)/2.
 * B_n = { |j| <= n, |x| <= n }. Boundary sites of B_n are black (wired).
 * I_n = black cluster of the boundary. A "hole" is a component of B_n \ I_n.
 * D_n holds iff no hole contains both an axis site (i,0), -n < i <= 0,
 * and a site with x > 0. (Self-matching: the outer boundary of a hole is a
 * white circuit, and it contains the rightmost site of the hole.)
 * Nested boxes n = 8,16,...,N evaluated on one configuration.
 * Output per sample: bitmask of D_n and bitmask of (0 in I_n).
 * Pinch cuts (default on): the step c->d between non-I sites is forbidden when both
 * common neighbours of c and d lie in I (a white circuit using it would enclose an I site).
 * w18: target X_theta = {|arg z| < theta} (theta in degrees, 0 = positive axis only).
 * usage: tri_wedge N samples seed pinch theta_deg [onesided]
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
static double TH; static int ONES=0; /* ONES=1: X_theta^+ = X_theta ∩ {y >= 0} */
/* site (i,j) lies in X_theta: x=i+j/2, y=j*sqrt(3)/2 */
static int inX(int i,int j){ double x=i+0.5*j, y=0.8660254037844386*j; if(ONES && y<0) return 0; if(y==0.0) return x>0; double a=atan2(fabs(y),x); return a < TH-1e-12; }

static uint64_t s[2];
static uint64_t nx(void){uint64_t a=s[0],b=s[1];s[0]=b;a^=a<<23;s[1]=a^b^(a>>17)^(b>>26);return s[1]+b;}

static int N, W; static int pinch=1; static unsigned char *col; static int *mark; static int *q; static int stamp=0;
#define ID(i,j) (((j)+N)*W+((i)+2*N))
static int inbox(int i,int j,int n){ if(j<-n||j>n) return 0; int x2=2*i+j; return x2>=-2*n && x2<=2*n; }
static int isbd(int i,int j,int n){ if(!inbox(i,j,n)) return 0;
  static const int d[6][2]={{1,0},{-1,0},{0,1},{0,-1},{1,-1},{-1,1}};
  for(int k=0;k<6;k++) if(!inbox(i+d[k][0],j+d[k][1],n)) return 1; return 0; }

int main(int argc,char**argv){
  N=atoi(argv[1]); if(argc>4) pinch=atoi(argv[4]); TH=(argc>5?atof(argv[5]):90.0)*M_PI/180.0; if(argc>6) ONES=atoi(argv[6]); int S=atoi(argv[2]); s[0]=atoll(argv[3])*0x9E3779B97F4A7C15ULL+1; s[1]=0xdeadbeef^s[0]; for(int k=0;k<20;k++)nx();
  W=4*N+1; int H=2*N+1; col=malloc(W*H); mark=malloc(sizeof(int)*W*H); int *hole=malloc(sizeof(int)*W*H); q=malloc(sizeof(int)*W*H);
  memset(mark,0,sizeof(int)*W*H); memset(hole,0,sizeof(int)*W*H);
  static const int d[6][2]={{1,0},{0,1},{-1,1},{-1,0},{0,-1},{1,-1}}; /* cyclic */
  for(int t=0;t<S;t++){
    for(int k=0;k<W*H;k++){ col[k]=(nx()>>63)&1; }
    unsigned Dm=0, Pm=0; int bit=0;
    for(int n=8;n<=N;n*=2,bit++){
      int st=++stamp; int h=0,tl=0;
      /* I_n: BFS over black sites from boundary (boundary counts black) */
      for(int j=-n;j<=n;j++) for(int i=-2*n;i<=2*n;i++) if(isbd(i,j,n)){ int id=ID(i,j); if(mark[id]!=st){mark[id]=st;q[tl++]=id;} }
      while(h<tl){ int id=q[h++]; int j=id/W-N, i=id%W-2*N;
        for(int k=0;k<6;k++){int a=i+d[k][0],b=j+d[k][1]; if(!inbox(a,b,n))continue; int e=ID(a,b); if(mark[e]==st||!col[e])continue; mark[e]=st;q[tl++]=e;} }
      if(mark[ID(0,0)]==st) Pm|=1u<<bit;
      /* flood non-I sites from all non-I sites with x>0 */
      int hs=st; h=0; tl=0;
      for(int j=-n;j<=n;j++) for(int i=-2*n;i<=2*n;i++){ if(!inbox(i,j,n)) continue; if(!inX(i,j)) continue; int id=ID(i,j); if(mark[id]!=st && hole[id]!=hs){hole[id]=hs;q[tl++]=id;} }
      while(h<tl){ int id=q[h++]; int j=id/W-N, i=id%W-2*N;
        for(int k=0;k<6;k++){int a=i+d[k][0],b=j+d[k][1]; if(!inbox(a,b,n))continue; int e=ID(a,b); if(mark[e]==st||hole[e]==hs)continue;
          if(pinch){ int k1=(k+5)%6,k2=(k+1)%6; int a1=i+d[k1][0],b1=j+d[k1][1],a2=i+d[k2][0],b2=j+d[k2][1];
            int i1=!inbox(a1,b1,n)||mark[ID(a1,b1)]==st, i2=!inbox(a2,b2,n)||mark[ID(a2,b2)]==st; if(i1&&i2) continue; }
          hole[e]=hs;q[tl++]=e;} }
      int ok=1; for(int i=-n+1;i<=0;i++){ int id=ID(i,0); if(mark[id]!=st && hole[id]==hs){ok=0;break;} }
      if(ok) Dm|=1u<<bit;
    }
    printf("%u %u\n",Dm,Pm); fflush(stdout);
  }
  return 0;
}
