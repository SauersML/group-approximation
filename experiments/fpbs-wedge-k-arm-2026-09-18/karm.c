/* w19-123: single-wedge K-arm events vs the FPBS pinch-wall box events.
 * Triangular site percolation p=1/2, axial coords (i,j), x=i+j/2, y=j*sqrt(3)/2,
 * B_n = {|j|<=n, |2i+j|<=2n}, boundary black (wired), I_n = black cluster of boundary
 * (same conventions as tri_wedge.c of w18-123).
 * K-connectivity on I_n: ordinary adjacency plus "jumps" a->a+d[k]+d[k+1] (the far
 * corner of a rhombus) between two I_n sites.
 * A_W: K-path of I_n sites inside the closed wedge W from the origin (in I_n) to a
 * boundary site of B_n.  Wedges: 0 UL {y>=0,x<=0}, 1 LL {y<=0,x<=0}, 2 UH {y>=0}, 3 LH {y<=0}.
 * D'_n(Y): no pinch-free non-I_n path from a site of S_n={(i,0):-n<i<=0} to Y.
 *   Y=X_{pi/2}={x>0} (bit 4), Y=positive axis (bit 5).  bit 6: origin in I_n.
 * Output per sample: 7 bitmasks over nested n=8,16,...,N.
 * usage: karm N samples seed [mode]
 * mode 1 (fast): columns 4,5 are instead A_UR {y>=0,x>=0} and A_LR {y<=0,x>=0} (the mirror
 * images of UL, LL under x -> -x), and D' is not computed.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static uint64_t s[2];
static uint64_t nx(void){uint64_t a=s[0],b=s[1];s[0]=b;a^=a<<23;s[1]=a^b^(a>>17)^(b>>26);return s[1]+b;}
static int N,W; static unsigned char *col; static int *mark,*vis,*q; static int stamp=0;
#define ID(i,j) (((j)+N)*W+((i)+2*N))
static const int d[6][2]={{1,0},{0,1},{-1,1},{-1,0},{0,-1},{1,-1}}; /* cyclic */
static int inbox(int i,int j,int n){ if(j<-n||j>n) return 0; int x2=2*i+j; return x2>=-2*n && x2<=2*n; }
static int isbd(int i,int j,int n){ if(!inbox(i,j,n)) return 0;
  for(int k=0;k<6;k++) if(!inbox(i+d[k][0],j+d[k][1],n)) return 1; return 0; }
static int inW(int w,int i,int j){ int x2=2*i+j;
  switch(w){case 0: return j>=0&&x2<=0; case 1: return j<=0&&x2<=0; case 2: return j>=0; case 3: return j<=0;
    case 4: return j>=0&&x2>=0; default: return j<=0&&x2>=0;} }
static int st; /* current I_n stamp */
static int isI(int i,int j,int n){ return !inbox(i,j,n) || mark[ID(i,j)]==st; }
/* K-arm in wedge w from origin to boundary */
static int karm(int w,int n){
  if(mark[ID(0,0)]!=st) return 0;
  int vs=++stamp,h=0,tl=0; vis[ID(0,0)]=vs; q[tl++]=ID(0,0);
  while(h<tl){ int id=q[h++]; int j=id/W-N,i=id%W-2*N; if(isbd(i,j,n)) return 1;
    for(int k=0;k<12;k++){ int a,b;
      if(k<6){a=i+d[k][0];b=j+d[k][1];} else {int k1=k-6,k2=(k1+1)%6; a=i+d[k1][0]+d[k2][0]; b=j+d[k1][1]+d[k2][1];}
      if(!inbox(a,b,n)||!inW(w,a,b)) continue; int e=ID(a,b); if(mark[e]!=st||vis[e]==vs) continue;
      vis[e]=vs; q[tl++]=e; } }
  return 0;
}
/* D'_n(Y): y=0 -> {x>0}, y=1 -> positive axis */
static int dprime(int y,int n){
  int hs=++stamp,h=0,tl=0;
  for(int j=-n;j<=n;j++) for(int i=-2*n;i<=2*n;i++){ if(!inbox(i,j,n)) continue;
    int in = y==0 ? (2*i+j>0) : (j==0 && i>0); if(!in) continue; int id=ID(i,j);
    if(mark[id]!=st && vis[id]!=hs){vis[id]=hs;q[tl++]=id;} }
  while(h<tl){ int id=q[h++]; int j=id/W-N,i=id%W-2*N;
    for(int k=0;k<6;k++){ int a=i+d[k][0],b=j+d[k][1]; if(!inbox(a,b,n)) continue; int e=ID(a,b);
      if(mark[e]==st||vis[e]==hs) continue;
      int k1=(k+5)%6,k2=(k+1)%6;
      if(isI(i+d[k1][0],j+d[k1][1],n)&&isI(i+d[k2][0],j+d[k2][1],n)) continue; /* pinch */
      vis[e]=hs; q[tl++]=e; } }
  for(int i=-n+1;i<=0;i++){ int id=ID(i,0); if(mark[id]!=st && vis[id]==hs) return 0; }
  return 1;
}
int main(int argc,char**argv){
  N=atoi(argv[1]); int S=atoi(argv[2]); int mode=argc>4?atoi(argv[4]):0; s[0]=atoll(argv[3])*0x9E3779B97F4A7C15ULL+1; s[1]=0xdeadbeef^s[0]; for(int k=0;k<20;k++)nx();
  W=4*N+1; int H=2*N+1; col=malloc(W*H); mark=calloc(W*H,sizeof(int)); vis=calloc(W*H,sizeof(int)); q=malloc(sizeof(int)*W*H*2);
  for(int t=0;t<S;t++){
    for(int k=0;k<W*H;k++) col[k]=(nx()>>63)&1;
    unsigned m[7]={0}; int bit=0;
    for(int n=8;n<=N;n*=2,bit++){
      st=++stamp; int h=0,tl=0;
      for(int j=-n;j<=n;j++) for(int i=-2*n;i<=2*n;i++) if(isbd(i,j,n)){int id=ID(i,j); if(mark[id]!=st){mark[id]=st;q[tl++]=id;}}
      while(h<tl){ int id=q[h++]; int j=id/W-N,i=id%W-2*N;
        for(int k=0;k<6;k++){int a=i+d[k][0],b=j+d[k][1]; if(!inbox(a,b,n))continue; int e=ID(a,b); if(mark[e]==st||!col[e])continue; mark[e]=st;q[tl++]=e;} }
      for(int w=0;w<4;w++) if(karm(w,n)) m[w]|=1u<<bit;
      if(mode==1){ if(karm(4,n)) m[4]|=1u<<bit; if(karm(5,n)) m[5]|=1u<<bit; }
      else { if(dprime(0,n)) m[4]|=1u<<bit; if(dprime(1,n)) m[5]|=1u<<bit; }
      if(mark[ID(0,0)]==st) m[6]|=1u<<bit;
    }
    printf("%u %u %u %u %u %u %u\n",m[0],m[1],m[2],m[3],m[4],m[5],m[6]); fflush(stdout);
  }
  return 0;
}
