/* Exhaustive check at small n of the increasing half-plane decomposition:
 *   U = no pinch-free non-I_n path inside {j>=0} from S_n to the positive axis,
 *   L = the same inside {j<=0}.
 * Checks, over all colourings of the interior of B_n:
 *   (1) D'_n(0) == U && L            (every configuration)
 *   (2) on C_n: A_n(UH) == U and A_n(LH) == L
 *   (3) local forcing: U implies 0 in I or (1,0) in I or {(0,1),(1,-1)} in I
 *   (4) flip: on D'_n(0) (resp. U) with 0 not in I, colouring 0 black gives C_n and keeps D'_n(0) (resp. U)
 * and prints exact P(C), P(U), P(C&U), P(D'), P(D'&C), kappa_H.
 * usage: dec n            (exhaustive)
 *        dec n samples seed (Monte Carlo, same checks) */
#define main karm_main
#include "../fpbs-wedge-k-arm-2026-09-18/karm.c"
#undef main
static int in_[1<<17],m_;
static void cluster(int n){ st=++stamp; int h=0,tl=0;
  for(int j=-n;j<=n;j++) for(int i=-2*n;i<=2*n;i++) if(isbd(i,j,n)){int id=ID(i,j); if(mark[id]!=st){mark[id]=st;q[tl++]=id;}}
  while(h<tl){ int id=q[h++]; int j=id/W-N,i=id%W-2*N;
    for(int k=0;k<6;k++){int a=i+d[k][0],b=j+d[k][1]; if(!inbox(a,b,n))continue; int e=ID(a,b); if(mark[e]==st||!col[e])continue; mark[e]=st;q[tl++]=e;} } }
/* side=+1: sites with j>=0; side=-1: j<=0. Returns 1 if the "no path" event holds. */
static int half(int side,int n){ int hs=++stamp,h=0,tl=0;
  for(int i=-n+1;i<=0;i++){ int id=ID(i,0); if(mark[id]!=st){ vis[id]=hs; q[tl++]=id; } }
  while(h<tl){ int id=q[h++]; int j=id/W-N,i=id%W-2*N; if(j==0&&i>=1) return 0;
    for(int k=0;k<6;k++){ int a=i+d[k][0],b=j+d[k][1]; if(!inbox(a,b,n)||side*b<0) continue; int e=ID(a,b);
      if(mark[e]==st||vis[e]==hs) continue;
      int k1=(k+5)%6,k2=(k+1)%6;
      if(isI(i+d[k1][0],j+d[k1][1],n)&&isI(i+d[k2][0],j+d[k2][1],n)) continue;
      vis[e]=hs; q[tl++]=e; } }
  return 1; }
int main(int argc,char**argv){
  int n=atoi(argv[1]); N=n; W=4*N+1; int H=2*N+1;
  col=calloc(W*H,1); mark=calloc(W*H,sizeof(int)); vis=calloc(W*H,sizeof(int)); q=malloc(sizeof(int)*W*H*2);
  for(int j=-n;j<=n;j++) for(int i=-2*n;i<=2*n;i++) if(inbox(i,j,n)&&!isbd(i,j,n)) in_[m_++]=ID(i,j);
  fprintf(stderr,"interior sites %d\n",m_);
  long long cC=0,cU=0,cCU=0,cD=0,cDC=0,cUH=0,cLH=0,cUHLH=0,v1=0,v2=0,v3=0,v4=0,v5=0; long long tot=1LL<<m_; int mc=argc>2; if(mc){ tot=atoll(argv[2]); s[0]=atoll(argv[3])*0x9E3779B97F4A7C15ULL+1; s[1]=0xdeadbeef^s[0]; for(int k=0;k<20;k++)nx(); }
  for(long long z=0;z<tot;z++){
    for(int k=0;k<m_;k++) col[in_[k]]= mc ? (nx()>>63)&1 : (z>>k)&1;
    cluster(n);
    int C=mark[ID(0,0)]==st, U=half(1,n), L=half(-1,n), Dp=dprime(1,n);
    if(Dp!=(U&&L)) v1++;
    if(U && !(isI(0,0,n)||isI(1,0,n)||(isI(0,1,n)&&isI(1,-1,n)))) v3++;
    cC+=C; cU+=U; cCU+=C&&U; cD+=Dp; cDC+=Dp&&C;
    if(C){ int a2=karm(2,n),a3=karm(3,n); cUH+=a2; cLH+=a3; cUHLH+=a2&&a3; if(a2!=U||a3!=L) v2++; }
    if(!C&&(U||Dp)){ int c0=col[ID(0,0)]; col[ID(0,0)]=1; cluster(n);
      int C2=mark[ID(0,0)]==st, U2=half(1,n), D2=dprime(1,n);
      if(U&&!(C2&&U2)) v4++; if(Dp&&!(C2&&D2)) v5++; col[ID(0,0)]=c0; }
  }
  double T=(double)tot;
  printf("n=%d configs=%lld C=%.6f U=%.6f C&U=%.6f D'=%.6f D'&C=%.6f UH=%.6f UH&LH=%.6f kappaH=%.6f\n",n,tot,
    cC/T,cU/T,cCU/T,cD/T,cDC/T,cUH/T,cUHLH/T,(double)cUHLH*cC/((double)cUH*cLH));
  printf("violations: (1) D'!=U&L %lld  (2) A(UH)!=C&U on C %lld  (3) local forcing %lld  (4) flip U %lld  flip D' %lld\n",v1,v2,v3,v4,v5);
  return 0;
}
