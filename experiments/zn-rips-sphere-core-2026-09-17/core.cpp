// Sphere hard core: symmetric D-move iteration on sphere points of B_r in Z^n.
#include <bits/stdc++.h>
using namespace std;
int n, r;
vector<vector<int>> ball;
map<vector<int>,int> repid; vector<vector<int>> reps; vector<char> deleted;
vector<int> sortabs(const vector<int>& y){ vector<int> a(n); for(int i=0;i<n;i++) a[i]=abs(y[i]); sort(a.rbegin(),a.rend()); return a; }
void genball(vector<int>& cur,int i,int rem){ if(i==n){ ball.push_back(cur); return;} for(int v=-rem;v<=rem;v++){cur[i]=v; genball(cur,i+1,rem-abs(v));} }
void genreps(vector<int>& cur,int i,int rem,int mx){ if(i==n){ if(rem==0){repid[cur]=reps.size(); reps.push_back(cur);} return;} for(int v=min(rem,mx);v>=0;v--){cur[i]=v; genreps(cur,i+1,rem-v,v);} }
int main(int argc,char**argv){ n=atoi(argv[1]); r=atoi(argv[2]); vector<int> cur(n); genball(cur,0,r); genreps(cur,0,r,r); deleted.assign(reps.size(),0);
  vector<int> normv(ball.size()), rid(ball.size(),-1);
  for(size_t i=0;i<ball.size();i++){ int s=0; for(int v:ball[i]) s+=abs(v); normv[i]=s; if(s==r) rid[i]=repid[sortabs(ball[i])]; }
  fprintf(stderr,"n=%d r=%d |B|=%zu reps=%zu\n",n,r,ball.size(),reps.size());
  bool changed=true; int round=0;
  while(changed){ changed=false; round++; vector<int> todel;
    for(size_t k=0;k<reps.size();k++){ if(deleted[k]) continue; const auto& x=reps[k];
      vector<int> nb; for(size_t i=0;i<ball.size();i++){ if(rid[i]>=0 && deleted[rid[i]]) continue; int d=0; for(int j=0;j<n;j++) d+=abs(x[j]-ball[i][j]); if(d<=r) nb.push_back(i);} 
      int supp=0; for(int j=0;j<n;j++) if(x[j]) supp|=1<<j; int cover=0;
      vector<int> w(n,0);
      // enumerate w in hull(0,x), w!=x
      function<void(int)> rec=[&](int j){ if(j==n){ if(w==x) return; int ws=0; for(int t=0;t<n;t++) if(w[t]) ws|=1<<t; if((cover|ws)==cover) return; 
          for(int i:nb){ int d=0; for(int t=0;t<n;t++) d+=abs(w[t]-ball[i][t]); if(d>r) return; }
          cover|=ws; return;} for(int v=0;v<=x[j];v++){w[j]=v; rec(j+1);} };
      rec(0);
      if(cover==supp) todel.push_back(k);
    }
    for(int k:todel){deleted[k]=1; changed=true;}
    fprintf(stderr,"round %d deleted %zu\n",round,todel.size());
  }
  int left=0; for(size_t k=0;k<reps.size();k++) if(!deleted[k]){ left++; printf("core:"); for(int v:reps[k]) printf(" %d",v); printf("\n"); }
  printf("n=%d r=%d reps=%zu core_reps=%d\n",n,r,reps.size(),left);
}
