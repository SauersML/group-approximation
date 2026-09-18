// Partition-level check of the slack-1 extension of the sphere criterion for VR(Z^n, d_1; r).
// U = unbalanced partitions of r into at most n parts (complete search as in sphere_nop2.cpp).
// For x in U (as a vector in Z_{>=0}^n, nonincreasing) and each support index k, look for y with 0 <= y <= x,
// y != 0, y != x, y_k >= 1, slack-1 balanced (<sg,y> <= max(1,<sg,x>) for all sg on supp x), and such that NO
// z in Z^n whose magnitude partition lies in U has |z - x| <= r and |z - y| > r (|z| = r automatically).
// Only for (n,r) where every unbalanced partition has exactly n parts: then x and every candidate z have full support,
// x_n > 0 and z_n > 0 (z > 0 in the link), and in the normalized frame the last lattice coordinate is the index k.
// Prints, per (n,r), |U| and the number of (x,k) without such y. Exit 0 iff every (x,k) has one.
// Usage: ./slack_crit n rmin rmax [printU]
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
vector<vector<int>> U;
vector<int> X, Y, cnt; vector<int> vals; int P, K; bool hit; vector<int> sufx, sufy, sufd;
void zrec(int i,int A,int B){ if(hit) return;
  if(A+sufy[i]<1 || B-sufx[i]>0 || A-B+sufd[i]<1) return;   // per coordinate: a<=y_i, b>=-x_i, a-b<=x_i-y_i
  if(i==n){ hit=true; return; }
  for(size_t q=0;q<vals.size();q++) if(cnt[q]){ int v=vals[q]; cnt[q]--;
    for(int sg: v? (i==K? vector<int>{1} : vector<int>{1,-1}) : vector<int>{1}){ int z=sg*v; zrec(i+1, A+abs(z-Y[i])-abs(z), B+abs(z-X[i])-abs(z)); if(hit) break; }
    cnt[q]++; if(hit) return; } }
bool unbalanced_z_fails(){ for(auto& p:U){ map<int,int> mm; for(int v:p) mm[v]++; mm[0]+=n-p.size(); vals.clear(); cnt.clear(); for(auto& kv:mm){ vals.push_back(kv.first); cnt.push_back(kv.second); }
    hit=false; zrec(0,0,0); if(hit) return true; } return false; }
int main(int argc,char**argv){
  // Sharded mode: ./slack_shard n r ufile shard nshards   (U read from the "U r=<r>: ..." line printed by slack_crit_u;
  // x ranges over the partitions with index % nshards == shard, z over all of U)
  n=atoi(argv[1]); R=atoi(argv[2]); int shard=atoi(argv[4]), nsh=atoi(argv[5]);
  { ifstream f(argv[3]); string line; bool found=false; string tag="U r="+to_string(R)+":";
    while(getline(f,line)) if(line.rfind(tag,0)==0){ found=true; stringstream ss(line.substr(tag.size())); string tok;
      while(ss>>tok){ vector<int> p; stringstream ts(tok); string a; while(getline(ts,a,',')) p.push_back(stoi(a)); U.push_back(p);} }
    if(!found){ printf("no U line for r=%d\n",R); return 2; } }
  for(auto& p:U) if((int)p.size()!=n){ printf("n=%d r=%d: some unbalanced partition has fewer than n parts, not handled\n",n,R); return 1; }
  int fails=0, pairs=0;
  for(size_t pi=0;pi<U.size();pi++){ if((int)(pi%nsh)!=shard) continue; auto& p=U[pi];
    X=p; X.resize(n,0); int s=p.size(); sufx.assign(n+1,0); for(int i=n-1;i>=0;i--) sufx[i]=sufx[i+1]+X[i];
    for(int k=0;k<s;k++){ if(k>0&&X[k]==X[k-1]) continue; pairs++; K=k; bool ok=false; Y.assign(n,0);
      function<void(int)> yrec=[&](int i){ if(ok) return; if(i==s){ int t=0; for(int v:Y) t+=v; if(t==0||t==R||Y[k]<1) return; if(!balS(X,Y,1)) return;
          sufy.assign(n+1,0); for(int j=n-1;j>=0;j--) sufy[j]=sufy[j+1]+Y[j]; sufd.assign(n+1,0); for(int j=n-1;j>=0;j--) sufd[j]=sufd[j+1]+X[j]-Y[j];
          if(!unbalanced_z_fails()){ ok=true; } return; }
        for(int v=0;v<=X[i];v++){ Y[i]=v; yrec(i+1); if(ok) return; } Y[i]=0; };
      yrec(0);
      if(!ok){ fails++; if(fails<=3){ printf("  no y for x=("); for(int i=0;i<s;i++) printf("%d%s",X[i],i+1<s?",":""); printf(") k=%d\n",k); } } } }
  printf("n=%d r=%d unbalanced=%zu shard=%d/%d (x,k)=%d without-y=%d\n",n,R,U.size(),shard,nsh,pairs,fails); fflush(stdout);
  return fails?1:0; }
