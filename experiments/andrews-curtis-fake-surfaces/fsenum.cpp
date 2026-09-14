// fsenum.cpp -- enumerate acyclic cellular fake surfaces of complexity t (lane hl-andrews-curtis).
// Model: singular graph = connected 4-regular multigraph (loops count 2); at each vertex the 6 sheet
// corners are the pairs of its 4 half-edges; along each edge a bijection (6 choices) matches the 3
// corners at one end with the 3 at the other. Disks = corner cycles (each boundary circle traversed
// in two directions). Acyclic <=> exactly t+1 disks and det(exponent matrix after collapsing a tree)=+-1.
// Classes up to PL homeomorphism = orbits of half-edge graph automorphisms (orderly: keep min code).
#include <bits/stdc++.h>
#include <omp.h>
using namespace std;
typedef long long ll; typedef unsigned long long ull;
static const int P[6][3]={{0,1,2},{0,2,1},{1,0,2},{1,2,0},{2,0,1},{2,1,0}};
int pidx(int a,int b,int c){ for(int i=0;i<6;i++) if(P[i][0]==a&&P[i][1]==b&&P[i][2]==c) return i; return -1; }

struct G {
  int t,E,H,S; vector<vector<int>> A; vector<int> vert; vector<array<int,3>> oth;
  vector<int> tree, gen; vector<vector<int>> rev; // rev[y][h] = index of h in oth[y]
  vector<vector<int>> autCS; // corner-state permutations induced by half-edge automorphisms
};

vector<vector<vector<int>>> graphs(int t){
  vector<pair<int,int>> pos; for(int i=0;i<t;i++) for(int j=i;j<t;j++) pos.push_back({i,j});
  vector<vector<int>> A(t,vector<int>(t,0)); vector<int> rs(t,0); set<vector<int>> canon;
  vector<int> perm(t);
  function<void(size_t)> rec=[&](size_t p){
    if(p==pos.size()){
      for(int v=0;v<t;v++) if(rs[v]!=4) return;
      vector<int> seen(t,0),st={0}; seen[0]=1;
      while(!st.empty()){int u=st.back();st.pop_back();for(int w=0;w<t;w++) if(A[u][w]&&!seen[w]){seen[w]=1;st.push_back(w);} }
      for(int v=0;v<t;v++) if(!seen[v]) return;
      iota(perm.begin(),perm.end(),0); vector<int> best;
      do{ vector<int> c(t*t); for(int i=0;i<t;i++) for(int j=0;j<t;j++) c[i*t+j]=A[perm[i]][perm[j]];
          if(c>best) best=c; } while(next_permutation(perm.begin(),perm.end()));
      canon.insert(best); return;
    }
    auto [i,j]=pos[p];
    if(j==i && i>0 && rs[i-1]!=4) return;
    for(int x=0;x<=4;x++){
      if(i==j){ if(x%2) continue; if(rs[i]+x>4) break; A[i][i]=x; rs[i]+=x; rec(p+1); rs[i]-=x; A[i][i]=0; }
      else { if(rs[i]+x>4||rs[j]+x>4) break; A[i][j]=A[j][i]=x; rs[i]+=x; rs[j]+=x; rec(p+1); rs[i]-=x; rs[j]-=x; A[i][j]=A[j][i]=0; }
    }
  };
  rec(0);
  vector<vector<vector<int>>> out;
  for(auto it=canon.rbegin(); it!=canon.rend(); ++it){ // decreasing D(A), as in Fagan-Qiu-Wang
    vector<vector<int>> B(t,vector<int>(t)); for(int i=0;i<t;i++) for(int j=0;j<t;j++) B[i][j]=(*it)[i*t+j]; out.push_back(B);
  }
  return out;
}

G build(const vector<vector<int>>& A){
  G g; g.t=A.size(); g.A=A;
  for(int i=0;i<g.t;i++) for(int j=i;j<g.t;j++){ int m=(i==j)?A[i][i]/2:A[i][j];
    for(int k=0;k<m;k++){ g.vert.push_back(i); g.vert.push_back(j); } }
  g.H=g.vert.size(); g.E=g.H/2; g.S=3*g.H; assert(g.E==2*g.t);
  g.oth.resize(g.H); g.rev.assign(g.H,vector<int>(g.H,-1));
  for(int h=0;h<g.H;h++){ int c=0; for(int x=0;x<g.H;x++) if(x!=h&&g.vert[x]==g.vert[h]) g.oth[h][c++]=x; assert(c==3);
    for(int k=0;k<3;k++) g.rev[h][g.oth[h][k]]=k; }
  g.tree.assign(g.E,0); vector<int> seen(g.t,0); seen[0]=1; bool grew=true;
  while(grew){ grew=false; for(int e=0;e<g.E;e++){ int u=g.vert[2*e],w=g.vert[2*e+1];
    if(u!=w && seen[u]!=seen[w]){ seen[u]=seen[w]=1; g.tree[e]=1; grew=true; } } }
  g.gen.assign(g.E,-1); int c=0; for(int e=0;e<g.E;e++) if(!g.tree[e]) g.gen[e]=c++; assert(c==g.t+1);
  vector<int> p(g.t); iota(p.begin(),p.end(),0);
  do{ bool ok=true; for(int u=0;u<g.t&&ok;u++) for(int w=0;w<g.t;w++) if(A[p[u]][p[w]]!=A[u][w]){ok=false;break;}
    if(!ok) continue;
    vector<int> phi(g.H,-1), used(g.E,0);
    function<void(int)> ar=[&](int e){
      if(e==g.E){ vector<int> cs(g.S);
        for(int h=0;h<g.H;h++) for(int k=0;k<3;k++) cs[3*h+k]=3*phi[h]+g.rev[phi[h]][phi[g.oth[h][k]]];
        g.autCS.push_back(cs); return; }
      for(int e2=0;e2<g.E;e2++) if(!used[e2]) for(int s=0;s<2;s++){
        int a=2*e2+s,b=2*e2+1-s; if(g.vert[a]!=p[g.vert[2*e]]||g.vert[b]!=p[g.vert[2*e+1]]) continue;
        phi[2*e]=a; phi[2*e+1]=b; used[e2]=1; ar(e+1); used[e2]=0; }
    };
    ar(0);
  } while(next_permutation(p.begin(),p.end()));
  return g;
}

inline void decode(const G& g, ull code, int* nxt){
  for(int e=0;e<g.E;e++){ int d=code%6; code/=6; int h0=2*e,h1=2*e+1;
    for(int k=0;k<3;k++){ nxt[3*h0+k]=3*h1+P[d][k]; nxt[3*h1+P[d][k]]=3*h0+k; } }
}
inline int step(const G& g,const int* nxt,int cs){ int nx=nxt[cs]; int h2=nx/3,y=g.oth[h2][nx%3]; return 3*y+g.rev[y][h2]; }
inline int revs(const G& g,int cs){ int h=cs/3,x=g.oth[h][cs%3]; return 3*x+g.rev[x][h]; }

ll det(ll M[8][8],int n){ ll prev=1; int sgn=1;
  for(int k=0;k<n-1;k++){ if(M[k][k]==0){ int r=k+1; while(r<n&&M[r][k]==0) r++; if(r==n) return 0; for(int j=0;j<n;j++) swap(M[r][j],M[k][j]); sgn=-sgn; }
    for(int i=k+1;i<n;i++) for(int j=k+1;j<n;j++) M[i][j]=(M[i][j]*M[k][k]-M[i][k]*M[k][j])/prev;
    prev=M[k][k]; }
  return sgn*M[n-1][n-1]; }

// returns minimal disk length (0 if not acyclic); fills words (signed edge letters, 1-based)
int analyse(const G& g, ull code, vector<vector<int>>* words){
  int nxt[96]; decode(g,code,nxt); bool vis[96]={0}; int disks=0,minlen=1<<30;
  ll M[8][8]={{0}};
  for(int s=0;s<g.S;s++){ if(vis[s]) continue; if(disks==g.t+1) return 0;
    int c=s,len=0; vector<int> w;
    do{ vis[c]=1; vis[revs(g,c)]=1; int h=c/3,e=h>>1; int sg=(h&1)?-1:1; if(g.gen[e]>=0) M[disks][g.gen[e]]+=sg;
        if(words) w.push_back(sg*(e+1)); len++; c=step(g,nxt,c); } while(c!=s);
    minlen=min(minlen,len); if(words) words->push_back(w); disks++; }
  if(disks!=g.t+1) return 0;
  ll d=det(M,g.t+1); return (d==1||d==-1)?minlen:0;
}

ull transform(const G& g,const vector<int>& cs,ull code){
  int nxt[96],nn[96]; decode(g,code,nxt);
  for(int s=0;s<g.S;s++) nn[cs[s]]=cs[nxt[s]];
  ull out=0,pw=1;
  for(int e=0;e<g.E;e++){ int h0=2*e; int q[3]; for(int k=0;k<3;k++){ int nx=nn[3*h0+k]; assert(nx/3==h0+1); q[k]=nx%3; }
    out+=pw*pidx(q[0],q[1],q[2]); pw*=6; }
  return out;
}

int main(int argc,char** argv){
  int t=atoi(argv[1]); string outp=argv[2];
  auto gs=graphs(t); fprintf(stderr,"t=%d graphs=%zu\n",t,gs.size());
  FILE* fo=fopen(outp.c_str(),"w"); ull totClasses=0,totNoSmall=0;
  for(size_t gi=0;gi<gs.size();gi++){
    G g=build(gs[gi]); ull N=1; for(int e=0;e<g.E;e++) N*=6;
    vector<vector<pair<ull,int>>> buf(omp_get_max_threads()); ull raw=0;
    #pragma omp parallel for schedule(dynamic,65536) reduction(+:raw)
    for(ull code=0;code<N;code++){
      int ml=analyse(g,code,nullptr); if(!ml) continue; raw++;
      bool keep=true; int stab=0;
      for(auto& cs:g.autCS){ ull c2=transform(g,cs,code); if(c2<code){keep=false;break;} if(c2==code) stab++; }
      if(keep) buf[omp_get_thread_num()].push_back({code,ml*1000+stab});
    }
    vector<pair<ull,int>> all; for(auto& b:buf) all.insert(all.end(),b.begin(),b.end()); sort(all.begin(),all.end());
    ull orbitSum=0,noSmall=0;
    for(auto& [code,info]:all){ int ml=info/1000,stab=info%1000; orbitSum+=g.autCS.size()/stab; if(ml>2) noSmall++;
      fprintf(fo,"%d %zu %llu %d\n",t,gi+1,code,ml); }
    fprintf(stderr,"graph %zu |Aut|=%zu raw=%llu classes=%zu noSmall=%llu orbitcheck=%s\n",gi+1,g.autCS.size(),raw,all.size(),noSmall,orbitSum==raw?"OK":"FAIL");
    totClasses+=all.size(); totNoSmall+=noSmall;
  }
  fclose(fo); fprintf(stderr,"TOTAL t=%d classes=%llu noSmall=%llu\n",t,totClasses,totNoSmall);
}
