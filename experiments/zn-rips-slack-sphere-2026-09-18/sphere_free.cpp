// ORDER-FREE point-level test (unbalanced sphere points stay in the current set). Otherwise as below:
// Point-level test of an ordered Stage 1: delete balanced sphere points first (Lemma 3), then each unbalanced
// sphere point x, looking for a dominator y in hull(0,x) against the CURRENT set (Lmax minus deleted sphere points).
// Usage: ./sphere_relax n r
#include <bits/stdc++.h>
using namespace std;
int n,r; vector<vector<int>> L; vector<char> del;
bool pos(const vector<int>& v){ for(int i=n-1;i>=0;i--) if(v[i]) return v[i]>0; return false; }
int nrm(const vector<int>& v){ int s=0; for(int a:v) s+=abs(a); return s; }
int d1(const vector<int>& a,const vector<int>& b){ int s=0; for(int i=0;i<n;i++) s+=abs(a[i]-b[i]); return s; }
void gen(vector<int>& cur,int i,int rem){ if(i==n){ if(pos(cur)) L.push_back(cur); return; } for(int v=-rem;v<=rem;v++){ cur[i]=v; gen(cur,i+1,rem-abs(v)); } }
// slack-balanced: <sg,|y|> <= max(slack, <sg,|x|>) for all sg  (slack=0: balanced)
bool bal(const vector<int>& x,const vector<int>& y,int slack){
  vector<int> sx, sy; for(int i=0;i<n;i++) if(x[i]){ sx.push_back(abs(x[i])); sy.push_back(abs(y[i])); }
  int s=sx.size();
  for(int mask=0; mask<(1<<s); mask++){ long long a=0,b=0; for(int i=0;i<s;i++){ int sg=(mask>>i&1)?1:-1; a+=sg*sx[i]; b+=sg*sy[i]; }
    if(b>max((long long)slack,a)) return false; }
  return true; }
bool dominates(const vector<int>& x,const vector<int>& y){ for(size_t j=0;j<L.size();j++){ if(del[j]) continue; auto& z=L[j]; if(d1(z,x)<=r && d1(z,y)>r) return false; } return true; }
vector<vector<int>> hull(const vector<int>& x){ vector<vector<int>> H; vector<int> y(n);
  function<void(int)> rec=[&](int i){ if(i==n){ if(y!=x && pos(y)) H.push_back(y); return; } int lo=min(0,x[i]),hi=max(0,x[i]); for(int v=lo;v<=hi;v++){ y[i]=v; rec(i+1);} }; rec(0); return H; }
int main(int argc,char**argv){ n=atoi(argv[1]); r=atoi(argv[2]); vector<int> cur(n); gen(cur,0,r); del.assign(L.size(),0);
  vector<int> unb; long long sph=0;
  for(size_t j=0;j<L.size();j++){ auto& x=L[j]; if(nrm(x)!=r) continue; sph++; bool ok=false; for(auto& y:hull(x)) if(bal(x,y,0)){ ok=true; break; }
    if(ok) del[j]=1; else unb.push_back(j); }
  long long slackok=0, otherok=0, fail=0, slackcand_fail=0;
  for(int j:unb){ auto& x=L[j]; auto H=hull(x); bool done=false; bool hadcand=false;
    for(auto& y:H) if(bal(x,y,1)){ hadcand=true; if(dominates(x,y)){ done=true; slackok++; break; } }
    if(!done){ if(hadcand) slackcand_fail++; for(auto& y:H) if(dominates(x,y)){ done=true; otherok++; break; } }
    if(!done){ fail++; if(fail<=5){ printf("  no dominator: ("); for(int i=0;i<n;i++) printf("%d%s",x[i],i+1<n?",":")\n"); } }
    }
  printf("n=%d r=%d |Lmax|=%zu sphere=%lld unbalanced=%zu slack1-dominated=%lld slack1-candidate-failed=%lld other-dominated=%lld undominated=%lld\n",n,r,L.size(),sph,unb.size(),slackok,slackcand_fail,otherok,fail);
  return fail?1:0; }
