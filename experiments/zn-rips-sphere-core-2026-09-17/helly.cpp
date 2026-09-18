// Search for a bad clique: sigma ⊆ B_r^+ minus B_{r/2}, pairwise d1<=r, such that no center
// y in B_{floor(r/2)}^+ ∩ hull(0 ∪ sigma) is within r of every point of sigma.
#include <bits/stdc++.h>
using namespace std;
int n,r,h; vector<vector<int>> P, Cn;
bool pos(const vector<int>& y){ for(int i=n-1;i>=0;i--) if(y[i]) return y[i]>0; return false; }
void gen(vector<int>& cur,int i,int rem,vector<vector<int>>& out,int lo){ if(i==n){ int s=0; for(int v:cur) s+=abs(v); if(pos(cur)&&s>=lo) out.push_back(cur); return;} for(int v=-rem;v<=rem;v++){cur[i]=v; gen(cur,i+1,rem-abs(v),out,lo);} }
int d1(const vector<int>&a,const vector<int>&b){int s=0; for(int i=0;i<n;i++) s+=abs(a[i]-b[i]); return s;}
unordered_set<uint64_t> seen; long long nodes=0; int found=0;
vector<vector<int>> killers; // per center: point ids with d>r
vector<vector<char>> adjm; // point adjacency (may be large)
int NP;
void dfs(vector<int>& sig, vector<int>& lo, vector<int>& hi){
  vector<int> s2=sig; sort(s2.begin(),s2.end()); uint64_t hsh=1469598103934665603ULL; for(int v:s2){hsh^=v; hsh*=1099511628211ULL;} if(!seen.insert(hsh).second) return; nodes++;
  if(nodes%1000000==0) fprintf(stderr,"nodes %lld depth %zu\n",nodes,sig.size());
  int best=-1; size_t bestc=SIZE_MAX; vector<int> bestlist;
  for(size_t c=0;c<Cn.size();c++){ const auto& y=Cn[c]; bool inh=true; for(int j=0;j<n;j++) if(y[j]<lo[j]||y[j]>hi[j]){inh=false;break;} if(!inh) continue;
    bool killed=false; for(int x:sig) if(d1(y,P[x])>r){killed=true;break;} if(killed) continue;
    vector<int> cand; for(int x:killers[c]){ bool ok=true; for(int z:sig) if(z==x||!adjm[x][z]){ok=false;break;} if(ok) cand.push_back(x); if(cand.size()>=bestc) break; }
    if(cand.size()<bestc){bestc=cand.size(); best=c; bestlist=cand; if(bestc==0) return;}
  }
  if(best<0){ found++; if(found<=5){ printf("BAD clique:"); for(int x:sig){printf(" ("); for(int v:P[x]) printf("%d,",v); printf(")");} printf("\n");} return; }
  for(int x:bestlist){ vector<int> lo2=lo,hi2=hi; for(int j=0;j<n;j++){lo2[j]=min(lo2[j],P[x][j]); hi2[j]=max(hi2[j],P[x][j]);} sig.push_back(x); dfs(sig,lo2,hi2); sig.pop_back(); if(found>=5) return; }
}
int main(int argc,char**argv){ n=atoi(argv[1]); r=atoi(argv[2]); h=r/2; vector<int> cur(n);
  vector<vector<int>> all; gen(cur,0,r,all,h+1); P=all; gen(cur,0,h,Cn,1); NP=P.size();
  fprintf(stderr,"n=%d r=%d |P|=%d |C|=%zu\n",n,r,NP,Cn.size());
  adjm.assign(NP,vector<char>(NP,0)); for(int i=0;i<NP;i++) for(int j=0;j<NP;j++) adjm[i][j]=(d1(P[i],P[j])<=r);
  killers.resize(Cn.size()); for(size_t c=0;c<Cn.size();c++) for(int i=0;i<NP;i++) if(d1(Cn[c],P[i])>r) killers[c].push_back(i);
  // root: branch over all points
  vector<int> sig, lo(n,0), hi(n,0);
  for(int x=0;x<NP;x++){ vector<int> lo2=lo,hi2=hi; for(int j=0;j<n;j++){lo2[j]=min(0,P[x][j]); hi2[j]=max(0,P[x][j]);} sig.push_back(x); dfs(sig,lo2,hi2); sig.pop_back(); if(found>=5) break; }
  printf("n=%d r=%d |P|=%d nodes=%lld bad_found=%d %s\n",n,r,NP,nodes,found, found? "C FAILS":"C HOLDS");
}
