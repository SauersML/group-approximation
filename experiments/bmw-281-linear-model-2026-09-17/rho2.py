# Ansatz: A0 = sigma, A1 = -sigma, A2 = -z; t0(z) = s*e*tw0(z) (e even unit), t1(z) = 1 + s*rho(z),
# t2 = A1 t1 A2; rho Moebius with rho^sigma = N rho N (optionally sigma-twisted).  T is then forced;
# test whether Phi tau Phi^-1 is semilinear Moebius (is_mob) on levels 2..M.
import sys, itertools
from ser import mul, inv, add, sub, sig, is_mob
from aut import AUT
M=int(sys.argv[1])
out, sec = AUT['281']
def run_aut(a, w):
    r=[]
    for x in w: r.append(out[a][x]); a=sec[a][x]
    return tuple(r)
def ev(al,be,ga,z,m,tw):
    if tw: z = sig(z)
    return mul(add(mul(al,z,m),be), inv(add(mul(ga,z,m),[1]+[0]*(m-1)),m), m)
def par(m, parity, lead):
    idx=[i for i in range(m) if i%2==parity]
    for v in itertools.product(range(3), repeat=len(idx)):
        if lead and v[0]==0: continue
        a=[0]*m
        for i,x in zip(idx,v): a[i]=x
        yield a
neg=lambda z:[(-v)%3 for v in z]
def build(e,tw0,a,b,c,tw,m):
    phis={0:{():()}}
    for k in range(1,m+1):
        d={}
        for w,p in phis[k-1].items():
            z=list(p)
            for x in range(3):
                if k==1: img=[x]
                elif x==0:
                    zz = sig(z) if tw0 else z
                    img=[0]+mul(e[:k-1],zz,k-1)
                elif x==1: img=[1]+ev(a[:k-1],b[:k-1],c[:k-1],z,k-1,tw)
                else:
                    # t2 = A1 t1 A2 : z -> -sigma(1 + s rho(-z))
                    r = [1]+ev(a[:k-1],b[:k-1],c[:k-1],neg(z),k-1,tw)
                    img = neg(sig(r))
                d[(x,)+w]=tuple(img)
        phis[k]=d
    return phis
def test(phis,m):
    for k in range(2,m+1):
        ph=phis[k]; inv_=dict((v,w) for w,v in ph.items())
        if len(inv_)!=3**k: return ('nb',k)
        pts=list(itertools.product(range(3),repeat=k)); idx={p:i for i,p in enumerate(pts)}
        for st in sorted(out):
            p=[idx[ph[run_aut(st,inv_[y])]] for y in pts]
            if is_mob(p,k,pts,lambda cc: idx[tuple(cc)]) is None: return (k,st)
    return True
from collections import Counter
fails=Counter(); n=0
for e in par(M,0,True):
  for tw0 in (0,1):
    for a in par(M,0,True):
      for b in par(M,1,False):
        for c in par(M,1,False):
          for tw in (0,1):
            r=test(build(e,tw0,a,b,c,tw,M),M)
            if r is True:
                n+=1
                if n<=10: print('SOL e',e,'tw0',tw0,'a',a,'b',b,'c',c,'tw',tw,flush=True)
            else: fails[r]+=1
print('solutions',n,'fails',fails.most_common(8))
