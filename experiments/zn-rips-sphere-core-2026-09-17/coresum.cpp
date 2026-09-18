// Exact half-ball sphere core: C = B_{r-1}^+ ∪ S^+_current, D-moves with w in hull(0,x), w ≻ 0.
#include <bits/stdc++.h>
using namespace std;
int n, r;
vector<vector<int>> ball;
bool posl(const vector<int>& y){ for(int i=n-1;i>=0;i--) if(y[i]) return y[i]>0; return false; }
bool pos(const vector<int>& y){ int s=0; for(int v:y) s+=v; if(s) return s>0; return posl(y);} 
void genball(vector<int>& cur,int i,int rem){ if(i==n){ if(pos(cur)) ball.push_back(cur); return;} for(int v=-rem;v<=rem;v++){cur[i]=v; genball(cur,i+1,rem-abs(v));} }
int main(int argc,char**argv){ n=atoi(argv[1]); r=atoi(argv[2]); vector<int> cur(n); genball(cur,0,r);
  int N=ball.size(); vector<int> normv(N); vector<int> sph; vector<char> alive(N,1);
  for(int i=0;i<N;i++){ int s=0; for(int v:ball[i]) s+=abs(v); normv[i]=s; if(s==r) sph.push_back(i);} 
  fprintf(stderr,"n=%d r=%d |B+|=%d |S+|=%zu\n",n,r,N,sph.size());
  bool changed=true; int round=0;
  while(changed){ changed=false; round++; vector<int> todel;
    for(int k:sph){ if(!alive[k]) continue; const auto& x=ball[k];
      vector<int> nb; for(int i=0;i<N;i++){ if(!alive[i]||i==k) continue; int d=0; for(int j=0;j<n;j++) d+=abs(x[j]-ball[i][j]); if(d<=r) nb.push_back(i);} 
      vector<int> w(n,0); bool ok=false;
      function<void(int)> rec=[&](int j){ if(ok) return; if(j==n){ if(w==x||!pos(w)) return; 
          for(int i:nb){ int d=0; for(int t=0;t<n;t++) d+=abs(w[t]-ball[i][t]); if(d>r) return; }
          ok=true; return;} int a=min(0,x[j]), b=max(0,x[j]); for(int v=a;v<=b;v++){w[j]=v; rec(j+1);} };
      rec(0);
      if(ok) todel.push_back(k);
    }
    for(int k:todel){alive[k]=0; changed=true;}
    fprintf(stderr,"round %d deleted %zu\n",round,todel.size());
  }
  int left=0; for(int k:sph) if(alive[k]){ left++; if(left<=40){printf("core:"); for(int v:ball[k]) printf(" %d",v); printf("\n");} }
  printf("n=%d r=%d |S+|=%zu core=%d\n",n,r,sph.size(),left);
}
