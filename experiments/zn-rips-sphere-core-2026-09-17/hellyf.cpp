// Center-condition search for VR(Z^n, d1; r).
// V = { y > 0 : |y| <= H + F[min(y_n^+, len F - 1)] }  (argv: n r H F0 F1 ...), checked to be a clique.
// S = points of B_r^+ not in V.  x > 0 means: last nonzero coordinate positive.
// Condition C: every clique sigma ⊆ S has a center y ∈ V ∩ hull(0 ∪ sigma) with d1(y,x) <= r for all x in sigma.
// Exact branch and bound: at a node sigma pick an alive hull center c; any bad superclique must contain a
// killer of c adjacent to all of sigma; branch on those.  Dedup by the exact sorted vertex list.
#include <bits/stdc++.h>
using namespace std;
int n,r,m,mode; vector<vector<int>> P, Cn;
bool pos(const vector<int>& y){ for(int i=n-1;i>=0;i--) if(y[i]) return y[i]>0; return false; }
void gen(vector<int>& cur,int i,int rem,vector<vector<int>>& out){ if(i==n){ if(pos(cur)) out.push_back(cur); return;} for(int v=-rem;v<=rem;v++){cur[i]=v; gen(cur,i+1,rem-abs(v),out);} }
int d1(const vector<int>&a,const vector<int>&b){int s=0; for(int i=0;i<n;i++) s+=abs(a[i]-b[i]); return s;}
int nrm(const vector<int>&a){int s=0; for(int v:a) s+=abs(v); return s;}
set<vector<int>> seen; long long nodes=0; int found=0; int NP; size_t maxdepth=0;
vector<vector<int>> killers; vector<vector<char>> adjm;
void dfs(vector<int>& sig, vector<int>& lo, vector<int>& hi){
  vector<int> s2=sig; sort(s2.begin(),s2.end()); if(!seen.insert(s2).second) return; nodes++; maxdepth=max(maxdepth,sig.size());
  if(nodes%200000==0) fprintf(stderr,"nodes %lld depth %zu\n",nodes,sig.size());
  int best=-1; size_t bestc=SIZE_MAX; vector<int> bestlist;
  for(size_t c=0;c<Cn.size();c++){ const auto& y=Cn[c]; bool inh=true; for(int j=0;j<n;j++) if(y[j]<lo[j]||y[j]>hi[j]){inh=false;break;} if(!inh) continue;
    bool killed=false; for(int x:sig) if(d1(y,P[x])>r){killed=true;break;} if(killed) continue;
    vector<int> cand; for(int x:killers[c]){ bool ok=true; for(int z:sig) if(z==x||!adjm[x][z]){ok=false;break;} if(ok){ cand.push_back(x); if(cand.size()>=bestc) break; } }
    if(cand.size()<bestc){bestc=cand.size(); best=c; bestlist=cand; if(bestc==0) return;}
  }
  if(best<0){ found++; if(found<=5){ printf("BAD clique:"); for(int x:sig){printf(" ("); for(int j=0;j<n;j++) printf("%d%s",P[x][j],j+1<n?",":""); printf(")");} printf("\n");} return; }
  for(int x:bestlist){ vector<int> lo2=lo,hi2=hi; for(int j=0;j<n;j++){lo2[j]=min(lo2[j],P[x][j]); hi2[j]=max(hi2[j],P[x][j]);} sig.push_back(x); dfs(sig,lo2,hi2); sig.pop_back(); if(found>=5) return; }
}
int H; vector<int> F; bool inVf(const vector<int>& y){ int a=max(0,y[n-1]); int fa=F[min(a,(int)F.size()-1)]; return nrm(y)<=H+fa; }
int main(int argc,char**argv){ n=atoi(argv[1]); r=atoi(argv[2]); mode=0; m=r/2; H=atoi(argv[3]); for(int i=4;i<argc;i++) F.push_back(atoi(argv[i])); if(F.empty()) F.push_back(0); vector<int> cur(n);
  vector<vector<int>> all; gen(cur,0,r,all);
  for(auto& y:all){ int s=nrm(y); bool inV = inVf(y); if(inV) Cn.push_back(y); else P.push_back(y); }
  NP=P.size();
  // sanity: V is a clique
  for(size_t a=0;a<Cn.size();a++) for(size_t b=0;b<Cn.size();b++) if(d1(Cn[a],Cn[b])>r){ fprintf(stderr,"V not a clique\n"); return 2; }
  fprintf(stderr,"n=%d r=%d mode=%d |S|=%d |V|=%zu\n",n,r,mode,NP,Cn.size());
  adjm.assign(NP,vector<char>(NP,0)); for(int i=0;i<NP;i++) for(int j=0;j<NP;j++) adjm[i][j]=(d1(P[i],P[j])<=r);
  killers.resize(Cn.size()); for(size_t c=0;c<Cn.size();c++) for(int i=0;i<NP;i++) if(d1(Cn[c],P[i])>r) killers[c].push_back(i);
  vector<int> sig, lo(n,0), hi(n,0);
  for(int x=0;x<NP;x++){ vector<int> lo2(n),hi2(n); for(int j=0;j<n;j++){lo2[j]=min(0,P[x][j]); hi2[j]=max(0,P[x][j]);} sig.push_back(x); dfs(sig,lo2,hi2); sig.pop_back(); if(found>=5) break; }
  printf("n=%d r=%d mode=%d |S|=%d |V|=%zu nodes=%lld maxdepth=%zu bad_found=%d %s\n",n,r,mode,NP,Cn.size(),nodes,maxdepth,found, found? "C FAILS":"C HOLDS");
}
