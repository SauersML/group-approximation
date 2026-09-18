// Point-level replay of the sphere criterion on Lmax = { x in Z^n : |x|_1 <= r, x > 0 }  (x > 0: last
// nonzero coordinate positive).  Independent of sphere_nop.cpp except for the NOP definition.
//  Phase 1: for every x in Lmax with |x|_1 = r, find y in hull(0,x) ∩ Lmax, y != x, satisfying NOP(x,y) and
//           check EXPLICITLY that every z in Lmax with d1(z,x) <= r has d1(z,y) <= r (D-move over all of Lmax).
//           If no NOP y exists, brute-force all y in hull(0,x) ∩ Lmax, y != x, with the explicit check.
//  Phase 2: for every x in Lmax with 2 <= |x|_1 <= r-1, check explicitly that e_k (k = last nonzero index)
//           is within r of every z in Lmax with |z|_1 <= |x|_1 (the current set when x is deleted).
// Prints counts; exit 0 iff every sphere point has an explicit dominator.
// Usage: ./sphere_check n r
#include <bits/stdc++.h>
using namespace std;
int n,r; vector<vector<int>> L;
bool pos(const vector<int>& v){ for(int i=n-1;i>=0;i--) if(v[i]) return v[i]>0; return false; }
int nrm(const vector<int>& v){ int s=0; for(int a:v) s+=abs(a); return s; }
int d1(const vector<int>& a,const vector<int>& b){ int s=0; for(int i=0;i<n;i++) s+=abs(a[i]-b[i]); return s; }
void gen(vector<int>& cur,int i,int rem){ if(i==n){ if(pos(cur)) L.push_back(cur); return; } for(int v=-rem;v<=rem;v++){ cur[i]=v; gen(cur,i+1,rem-abs(v)); } }
bool nop(const vector<int>& x,const vector<int>& y){ // magnitudes; <sg,|y|> between 0 and <sg,|x|> for all sg
  vector<int> sx, sy; for(int i=0;i<n;i++) if(x[i]){ sx.push_back(abs(x[i])); sy.push_back(abs(y[i])); }
  int s=sx.size();
  for(int mask=0; mask<(1<<s); mask++){ long long a=0,b=0; for(int i=0;i<s;i++){ int sg=(mask>>i&1)?1:-1; a+=sg*sx[i]; b+=sg*sy[i]; }
    if(b<min(0LL,a)||b>max(0LL,a)) return false; }
  return true; }
bool dominates(const vector<int>& x,const vector<int>& y){ for(auto& z:L) if(d1(z,x)<=r && d1(z,y)>r) return false; return true; }
bool found; vector<int> ybest;
void hullrec(const vector<int>& x, vector<int>& y, int i, bool wantnop){ if(found) return;
  if(i==n){ if(y==x || !pos(y)) return; if(wantnop){ if(nop(x,y)){ found=true; ybest=y; } } else if(dominates(x,y)){ found=true; ybest=y; } return; }
  int lo=min(0,x[i]), hi=max(0,x[i]); for(int v=lo; v<=hi; v++){ y[i]=v; hullrec(x,y,i+1,wantnop); if(found) return; } }
int main(int argc,char**argv){ n=atoi(argv[1]); r=atoi(argv[2]); vector<int> cur(n); gen(cur,0,r);
  long long sph=0, nopok=0, nopfail_explicit=0, realdom=0, undominated=0, interior_fail=0;
  vector<vector<int>> bad;
  for(auto& x:L){ if(nrm(x)!=r) continue; sph++;
    vector<int> y(n); found=false; hullrec(x,y,0,true);
    if(found){ nopok++; if(!dominates(x,ybest)) nopfail_explicit++; continue; }
    found=false; hullrec(x,y,0,false); if(found) realdom++; else { undominated++; if(bad.size()<5) bad.push_back(x); } }
  for(auto& x:L){ int s=nrm(x); if(s<2||s>=r) continue; int k=n-1; while(x[k]==0) k--; vector<int> e(n,0); e[k]=1;
    for(auto& z:L) if(nrm(z)<=s && d1(z,e)>r){ interior_fail++; break; } }
  printf("n=%d r=%d |Lmax|=%zu sphere=%lld NOP-dominated=%lld (explicit check failures %lld) real-dominated-without-NOP=%lld undominated=%lld interior_fail=%lld\n",
    n,r,L.size(),sph,nopok,nopfail_explicit,realdom,undominated,interior_fail);
  for(auto& x:bad){ printf("  undominated: ("); for(int i=0;i<n;i++) printf("%d%s",x[i],i+1<n?",":""); printf(")\n"); }
  return (undominated||nopfail_explicit||interior_fail)?1:0; }
