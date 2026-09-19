// Simulated annealing search for a usc level function on a product cell complex of I^N
// with two walls per coordinate, all of whose level components are "bad":
//   (T) bad:  3t + c(Omega) <= 3N-1   (c = total number of open chambers met)
//   (S) bad:  #coords not spanned > t
//   (B) bad:  c + t + 2*Tmax <= 3N-1  (Tmax = global max of delta)
// mode selects which property must fail everywhere. Usage: anneal N m Tmax mode steps seed
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
static int N,m,L,NC,TM,mode; static int *val,*del,*comp,*stk; static int pw[8];
static int chamber(int i){ if(i<2*m) return 0; if(i==2*m) return -1; if(i<4*m) return 1; if(i==4*m) return -1; return 2;}
static void coords(int c,int*a){for(int k=0;k<N;k++){a[k]=c%L;c/=L;}}
static unsigned long long rs=88172645463325252ULL; static unsigned long long rnd(){rs^=rs<<13;rs^=rs>>7;rs^=rs<<17;return rs;}
static int dimc(int c){int a[8];coords(c,a);int d=0;for(int k=0;k<N;k++)d+=a[k]&1;return d;}
static int *order;
static void closure(){ // delta = max over cofaces of val; process by decreasing dim
  for(int ii=0;ii<NC;ii++){int c=order[ii];int a[8];coords(c,a);int v=val[c];
    for(int k=0;k<N;k++) if(!(a[k]&1)){ if(a[k]>0){int d=del[c-pw[k]]; if(d>v)v=d;} if(a[k]<L-1){int d=del[c+pw[k]]; if(d>v)v=d;} }
    del[c]=v;}
}
static int nstat; static int statbuf[100000][4];
static long score(int verbose){
  closure(); int Tmax=0; for(int c=0;c<NC;c++) if(del[c]>Tmax)Tmax=del[c];
  memset(comp,-1,sizeof(int)*NC); long sc=0; int nc=0;
  for(int s=0;s<NC;s++) if(comp[s]<0){ int t=del[s]; int mask[8]; for(int k=0;k<N;k++)mask[k]=0;
    int sp=0; stk[sp++]=s; comp[s]=nc;
    while(sp){int c=stk[--sp]; int a[8];coords(c,a);
      for(int k=0;k<N;k++){int ch=chamber(a[k]); if(ch>=0) mask[k]|=1<<ch;}
      for(int k=0;k<N;k++){ for(int e=-1;e<=1;e+=2){ int b=a[k]+e; if(b<0||b>=L)continue; int c2=c+e*pw[k]; if(comp[c2]>=0||del[c2]!=t)continue; comp[c2]=nc; stk[sp++]=c2; } } }
    int cc=0,nsp=0; for(int k=0;k<N;k++){cc+=__builtin_popcount(mask[k]); if(mask[k]==7)nsp++;}
    long viol=0;
    if(mode==0){ viol=3*t+cc-(3*N-1); }
    else if(mode==1){ viol= (N-nsp) <= t ? 1+ t-(N-nsp) : 0; }
    else { viol= cc+t+2*Tmax-(3*N-1); }
    if(viol>0) sc+=viol;
    if(verbose) printf("comp %d level %d c %d spans %d viol %ld\n",nc,t,cc,nsp,viol>0?viol:0);
    nc++; }
  if(mode==2){ /* also penalise Tmax itself lightly */ }
  return sc;
}
int main(int argc,char**argv){N=atoi(argv[1]);m=atoi(argv[2]);TM=atoi(argv[3]);mode=atoi(argv[4]);long steps=atol(argv[5]);rs+=atoi(argv[6])*7919ULL;
  L=6*m+1; NC=1; for(int k=0;k<N;k++){pw[k]=NC;NC*=L;}
  val=calloc(NC,4);del=calloc(NC,4);comp=calloc(NC,4);stk=calloc(NC,4);order=calloc(NC,4);
  int o=0; for(int d=N;d>=0;d--) for(int c=0;c<NC;c++) if(dimc(c)==d) order[o++]=c;
  for(int c=0;c<NC;c++) val[c]=0;
  long cur=score(0),best=cur; double T0=atof(argc>7?argv[7]:"1.0");
  for(long it=0;it<steps&&cur>0;it++){ double temp=T0*(1.0-(double)it/steps)+0.05;
    int c=rnd()%NC; int old=val[c]; int nv=rnd()%(TM+1); if(nv==old)continue; val[c]=nv;
    long s=score(0); if(s<=cur || exp((cur-s)/temp) > (rnd()%1000000)/1e6){cur=s; if(s<best){best=s;}} else val[c]=old;
    if(it%20000==0){fprintf(stderr,"it %ld cur %ld best %ld\n",it,cur,best);} }
  printf("final score %ld best %ld\n",cur,best);
  if(cur==0){ score(1); FILE*f=fopen("found.txt","w"); for(int c=0;c<NC;c++) fprintf(f,"%d ",del[c]); fclose(f);} 
  return 0;}
