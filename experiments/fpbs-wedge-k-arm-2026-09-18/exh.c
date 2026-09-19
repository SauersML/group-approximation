/* Exhaustive enumeration over all colourings of the interior of B_n (small n):
 * exact P(A_UL), P(A_LL), P(A_UL&A_LL), P(A_UH), P(A_LH), P(A_UH&A_LH), P(0 in I_n).
 * usage: exh n */
#define main karm_main
#include "karm.c"
#undef main
int main(int argc,char**argv){
  int n=atoi(argv[1]); N=n; W=4*N+1; int H=2*N+1;
  col=calloc(W*H,1); mark=calloc(W*H,sizeof(int)); vis=calloc(W*H,sizeof(int)); q=malloc(sizeof(int)*W*H*2);
  int in[4096],m=0;
  for(int j=-n;j<=n;j++) for(int i=-2*n;i<=2*n;i++) if(inbox(i,j,n)&&!isbd(i,j,n)) in[m++]=ID(i,j);
  fprintf(stderr,"interior sites %d\n",m);
  long long c[8]={0}; long long tot=1LL<<m;
  for(long long z=0;z<tot;z++){
    for(int k=0;k<m;k++) col[in[k]]=(z>>k)&1;
    st=++stamp; int h=0,tl=0;
    for(int j=-n;j<=n;j++) for(int i=-2*n;i<=2*n;i++) if(isbd(i,j,n)){int id=ID(i,j); if(mark[id]!=st){mark[id]=st;q[tl++]=id;}}
    while(h<tl){ int id=q[h++]; int j=id/W-N,i=id%W-2*N;
      for(int k=0;k<6;k++){int a=i+d[k][0],b=j+d[k][1]; if(!inbox(a,b,n))continue; int e=ID(a,b); if(mark[e]==st||!col[e])continue; mark[e]=st;q[tl++]=e;} }
    if(mark[ID(0,0)]!=st) continue;
    int a0=karm(0,n),a1=karm(1,n),a2=karm(2,n),a3=karm(3,n);
    c[0]++; c[1]+=a0; c[2]+=a1; c[3]+=a0&a1; c[4]+=a2; c[5]+=a3; c[6]+=a2&a3; c[7]+=(a0&a1)&&!dprime(0,n);
  }
  double T=(double)tot;
  printf("n=%d C=%.6f UL=%.6f LL=%.6f UL&LL=%.6f kappaQ=%.6f UH=%.6f LH=%.6f UH&LH=%.6f kappaH=%.6f viol=%lld\n",n,
    c[0]/T,c[1]/T,c[2]/T,c[3]/T,(double)c[3]*c[0]/((double)c[1]*c[2]),c[4]/T,c[5]/T,c[6]/T,(double)c[6]*c[0]/((double)c[4]*c[5]),c[7]);
  return 0;
}
