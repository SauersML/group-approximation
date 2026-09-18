// Point-level check of the slack-one sphere criterion, with no full-support restriction.
// P = { x in Z^n : |x|_1 = r, x > 0 (last nonzero coordinate positive), magnitude partition of x unbalanced }.
// For every x in P look for y in hull(0,x), y != 0, y != x, y > 0, slack-one (<sg,|y|> <= max(1,<sg,|x|>) over supp x),
// such that NO z in P has |z - x| <= r and |z - y| > r.  z is enumerated by a pruned DFS over the arrangements of each
// unbalanced partition, assigning coordinates n-1..0 and forcing the first nonzero one assigned to be positive.
// ROUNDS: in each round every remaining x is tested against the REMAINING set P_t; all x that pass are deleted together
// (valid: domination against P_t implies domination against any subset). Repeats until P is empty or no x passes.
// Usage: ./sphere_rounds n r        Prints |U|, |P|, per-round deletions, and the number of x never deleted. Exit 0 iff none.
#include <bits/stdc++.h>
using namespace std;
int n, R;
bool balS(const vector<int>& x,const vector<int>& y,int slack){ int s=0; while(s<(int)x.size()&&x[s]) s++;
  for(int m=0;m<(1<<s);m++){ long long a=0,b=0; for(int i=0;i<s;i++){ int g=(m>>i&1)?1:-1; a+=g*x[i]; b+=g*y[i]; } if(b>max((long long)slack,a)) return false; } return true; }
bool good(const vector<int>& x){ int s=x.size(),N=0,g=0; for(int v:x){N+=v; g=__gcd(g,v);} if(g>1) return true;
  vector<int> y(s);
  for(int t=1;t<N;t++) for(int mode=0;mode<3;mode++){ int tot=0; for(int i=0;i<s;i++){ long long num=(long long)x[i]*t; int v= mode==0? num/N: mode==1? (num+N-1)/N : (2*num+N)/(2*N); y[i]=min(v,x[i]); tot+=y[i]; }
    if(tot==0||tot==N) continue; if(balS(x,y,0)) return true; }
  bool f=false; function<void(int,int)> rec=[&](int i,int used){ if(f) return; if(i==s){ if(used>0&&balS(x,y,0)) f=true; return; } for(int v=0;v<=x[i]&&used+v<=N/2;v++){ y[i]=v; rec(i+1,used+v); if(f) return; } };
  rec(0,0); return f; }
vector<vector<int>> U;             // unbalanced partitions, nonincreasing, length <= n
vector<vector<int>> vals, cnt0;    // per partition: distinct magnitudes (incl. 0) and multiplicities
vector<int> X, Y, cnt, Zc; unordered_set<long long> deleted;
long long enc(const vector<int>& v){ long long e=0; for(int a:v) e=e*(2*R+1)+(a+R); return e; } const vector<int>* V; bool hit; vector<int> preX, preY;
// assign coordinate i (going down), A = sum(|z-y|-|z|), B = sum(|z-x|-|z|) over assigned coords
void zrec(int i,int A,int B,bool started){ if(hit) return;
  if(A+preY[i+1]<1 || B-preX[i+1]>0) return;   // preY[i+1] = sum_{j<=i} |y_j|
  if(i<0){ if(!deleted.count(enc(Zc))) hit=true; return; }
  for(size_t q=0;q<V->size();q++) if(cnt[q]){ int v=(*V)[q]; cnt[q]--;
    if(v==0){ Zc[i]=0; zrec(i-1,A+abs(Y[i]),B+abs(X[i]),started); }
    else { for(int sg=1; sg>=-1; sg-=2){ if(!started && sg<0) break; int z=sg*v; Zc[i]=z; zrec(i-1,A+abs(z-Y[i])-abs(z),B+abs(z-X[i])-abs(z),true); if(hit) break; } }
    cnt[q]++; if(hit) return; } }
bool violated(){ preX.assign(n+1,0); preY.assign(n+1,0); for(int j=0;j<n;j++){ preX[j+1]=preX[j]+abs(X[j]); preY[j+1]=preY[j]+abs(Y[j]); }
  for(size_t p=0;p<U.size();p++){ V=&vals[p]; cnt=cnt0[p]; hit=false; zrec(n-1,0,0,false); if(hit) return true; } return false; }
int main(int argc,char**argv){ n=atoi(argv[1]); R=atoi(argv[2]);
  for(int s=1;s<=n;s++){ vector<int> x(s); function<void(int,int,int)> gen=[&](int i,int rem,int mx){ if(i==s){ if(!rem&&!good(x)) U.push_back(x); return; } for(int v=min(mx,rem-(s-i-1));v>=1;v--){ x[i]=v; gen(i+1,rem-v,v);} }; gen(0,R,R); }
  for(auto& p:U){ map<int,int> mm; for(int v:p) mm[v]++; mm[0]+=n-p.size(); vector<int> a,b; for(auto& kv:mm){ a.push_back(kv.first); b.push_back(kv.second);} vals.push_back(a); cnt0.push_back(b); }
  vector<vector<int>> Pts;
  for(size_t p=0;p<U.size();p++){
    vector<int> c=cnt0[p]; const vector<int>& vv=vals[p]; X.assign(n,0);
    function<void(int,bool)> xrec=[&](int i,bool started){
      if(i<0){ Pts.push_back(X); return; }
      for(size_t q=0;q<vv.size();q++) if(c[q]){ int v=vv[q]; c[q]--;
        if(v==0){ X[i]=0; xrec(i-1,started); }
        else for(int sg=1;sg>=-1;sg-=2){ if(!started&&sg<0) break; X[i]=sg*v; xrec(i-1,true); }
        c[q]++; } X[i]=0; };
    xrec(n-1,false); }
  Zc.assign(n,0);
  printf("n=%d r=%d unbalanced=%zu points=%zu\n",n,R,U.size(),Pts.size()); fflush(stdout);
  vector<char> gone(Pts.size(),0); size_t left=Pts.size(); int round=0;
  while(left){ vector<size_t> del;
    for(size_t t=0;t<Pts.size();t++){ if(gone[t]) continue; X=Pts[t];
      vector<int> supp; for(int j=0;j<n;j++) if(X[j]) supp.push_back(j);
      int s=supp.size(); vector<int> mag(s), ym(s); for(int u=0;u<s;u++) mag[u]=abs(X[supp[u]]);
      bool ok=false; Y.assign(n,0);
      function<void(int)> yrec=[&](int q){ if(ok) return;
        if(q==s){ int tot=0; for(int v:ym) tot+=v; if(tot==0||tot==R) return;
          int last=-1; for(int u=s-1;u>=0;u--) if(ym[u]){ last=u; break; } if(X[supp[last]]<0) return;
          if(!balS(mag,ym,1)) return;
          for(int u=0;u<s;u++) Y[supp[u]]= X[supp[u]]>0? ym[u] : -ym[u];
          if(!violated()) ok=true; return; }
        for(int v=0;v<=mag[q];v++){ ym[q]=v; yrec(q+1); if(ok) return; } };
      yrec(0);
      if(ok) del.push_back(t); }
    round++; printf("  round %d: deleted %zu of %zu\n",round,del.size(),left); fflush(stdout);
    if(del.empty()) break;
    for(size_t t:del){ gone[t]=1; deleted.insert(enc(Pts[t])); } left-=del.size(); }
  if(left){ int shown=0; for(size_t t=0;t<Pts.size()&&shown<5;t++) if(!gone[t]){ shown++; printf("  stuck x=("); for(int j=0;j<n;j++) printf("%d%s",Pts[t][j],j+1<n?",":")\n"); } }
  printf("n=%d r=%d unbalanced=%zu points=%zu rounds=%d never-deleted=%zu\n",n,R,U.size(),Pts.size(),round,left);
  return left?1:0; }
