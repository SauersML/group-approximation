// Shape-level test of the sphere criterion for VR(Z^n, d_1; r).
// A shape is x in Z_{>=1}^s (support magnitudes, nonincreasing).  x is GOOD iff there is an integer y with
// 0 <= y <= x, y != 0, y != x, and NOP(x,y): for every sign vector sg in {+-1}^s the number <sg,y>
// lies in the closed interval between 0 and <sg,x>.
// (Equivalently: no split J of the support with y(J) > y(J^c) and w(J) < w(J^c), where w = x - y.)
// By the symmetry y <-> x - y it suffices to search 1 <= |y| <= floor(|x|/2).
// If g = gcd(x) > 1 then y = x/g works.
// sphere_nop2: identical to sphere_nop.cpp except for an extra heuristic stage before the complete search:
// y = floor/round(x * t / N) for t = 1..N-1 (every candidate is verified by nop(), so the verdict is unchanged).
// Usage: ./sphere_nop2 s Nmin Nmax [printlimit]
#include <bits/stdc++.h>
using namespace std;
int s; vector<int> x, y;
bool nop(){ // <sg,v> = 2 v(J) - |v| where J = {sg = +1}
  static long long XJ[1<<12], YJ[1<<12]; int M=1<<s;
  XJ[0]=0; YJ[0]=0;
  for(int mask=1;mask<M;mask++){ int b=__builtin_ctz(mask); XJ[mask]=XJ[mask&(mask-1)]+x[b]; YJ[mask]=YJ[mask&(mask-1)]+y[b]; }
  long long TX=XJ[M-1], TY=YJ[M-1];
  for(int mask=0;mask<M;mask++){ long long a=2*XJ[mask]-TX, b=2*YJ[mask]-TY; if(b<min(0LL,a)||b>max(0LL,a)) return false; }
  return true; }
bool found; int H;
void rec(int i,int used){ if(found) return; if(i==s){ if(used>0 && nop()) found=true; return; }
  for(int v=0; v<=x[i] && used+v<=H; v++){ y[i]=v; rec(i+1,used+v); if(found) return; } }
bool good(){ int N=0,g=0; for(int v:x){N+=v; g=__gcd(g,v);} if(g>1) return true;
  H=N/2;
  vector<int> odd; for(int i=0;i<s;i++) if(x[i]&1) odd.push_back(i);
  for(long long m=0;m<(1LL<<odd.size());m++){ y.assign(s,0); int t=0; for(int i=0;i<s;i++) y[i]=x[i]/2;
    for(size_t j=0;j<odd.size();j++) if(m>>j&1) y[odd[j]]++; for(int v:y) t+=v; if(t==0||t==N) continue; if(nop()) return true; }
  for(int t=1;t<N;t++) for(int mode=0;mode<3;mode++){ int tot=0; y.assign(s,0);
    for(int i=0;i<s;i++){ long long num=(long long)x[i]*t; int v = mode==0? num/N : mode==1? (num+N-1)/N : (2*num+N)/(2*N); if(v>x[i]) v=x[i]; y[i]=v; tot+=v; }
    if(tot==0||tot==N) continue; if(nop()) return true; }
  y.assign(s,0); found=false; rec(0,0); return found; }
int main(int argc,char**argv){ s=atoi(argv[1]); int Nmin=atoi(argv[2]), Nmax=atoi(argv[3]); int plim=argc>4?atoi(argv[4]):3;
  x.assign(s,1);
  for(int N=max(Nmin,s); N<=Nmax; N++){ long long bad=0, tot=0; vector<vector<int>> ex;
    function<void(int,int,int)> gen=[&](int i,int rem,int mx){ if(i==s){ if(rem) return; tot++; if(!good()){ bad++; if((int)ex.size()<plim) ex.push_back(x);} return; }
      for(int v=min(mx,rem-(s-i-1)); v>=1; v--){ x[i]=v; gen(i+1,rem-v,v);} };
    gen(0,N,N);
    printf("s=%d N=%d shapes=%lld bad=%lld",s,N,tot,bad); for(auto&e:ex){ printf(" ("); for(int i=0;i<s;i++) printf("%d%s",e[i],i+1<s?",":""); printf(")"); } printf("\n"); fflush(stdout); }
}
