// Good(x,k): exists integer y with 0<=y<=x, y_k>=1, |y|<=floor(|x|/2), and NOP(x,y):
// no split J of supp(x) with y(J)>y(J^c) and w(J)<w(J^c), w=x-y.
// Enumerates x in Z_{>=1}^s nonincreasing (k ranges over all coordinates), |x| = N.
#include <bits/stdc++.h>
using namespace std;
int s; vector<int> x;
bool nop(const vector<int>& y){ int Y=0,W=0; for(int i=0;i<s;i++){Y+=y[i]; W+=x[i]-y[i];}
  for(int mask=1; mask<(1<<s)-1; mask++){ int yj=0,wj=0; for(int i=0;i<s;i++) if(mask>>i&1){yj+=y[i]; wj+=x[i]-y[i];}
    if(2*yj>Y && 2*wj<W) return false; }
  return true; }
bool found; vector<int> y; int K,H;
int RAD; // search radius around x/2 (RAD<0: full box)
void rec(int i,int used){ if(found) return; if(i==s){ if(y[K]>=1 && nop(y)){found=true;} return; }
  int lo=0,hi=x[i]; if(RAD>=0){ lo=max(0,x[i]/2-RAD); hi=min(x[i],(x[i]+1)/2+RAD); }
  for(int v=lo; v<=hi && used+v<=H; v++){ y[i]=v; rec(i+1,used+v); if(found) return; } }
int main(int argc,char**argv){ s=atoi(argv[1]); int Nmax=atoi(argv[2]);
  for(int N=s; N<=Nmax; N++){ int bad=0; vector<int> ex;
    // nonincreasing compositions of N into s parts >=1
    vector<int> c(s,1); function<void(int,int,int)> gen=[&](int i,int rem,int mx){ if(i==s){ if(rem) return; x=c;
        for(K=0;K<s;K++){ if(K>0 && x[K]==x[K-1]) continue; H=N/2; y.assign(s,0); found=false; RAD=1; rec(0,0); if(!found){RAD=-1; rec(0,0);} if(!found){ bad++; if(ex.empty()){ex=x; ex.push_back(K);} } } return; }
      for(int v=min(mx,rem-(s-i-1)); v>=1; v--){ c[i]=v; gen(i+1,rem-v,v);} };
    gen(0,N,N);
    printf("s=%d |x|=%d bad=%d",s,N,bad); if(!ex.empty()){ printf(" e.g. x=("); for(int i=0;i<s;i++) printf("%d%s",ex[i],i+1<s?",":""); printf(") k=%d",ex[s]); } printf("\n"); fflush(stdout);
  }
}
