# test one rho2 solution at levels 2..M and print the Moebius data of each generator
import sys, itertools
sys.argv=[sys.argv[0],'2']+sys.argv[1:]
exec(open('rho2.py').read().split('from collections')[0])
M=int(sys.argv[2])
def pad(v): return (v+[0]*M)[:M]
e=pad([1]);tw0=1;a=pad([1]);b=pad([]);c=pad([0,1]);tw=1
phis=build(e,tw0,a,b,c,tw,M)
for k in range(2,M+1):
    ph=phis[k]; inv_=dict((v,w) for w,v in ph.items())
    pts=list(itertools.product(range(3),repeat=k)); idx={p:i for i,p in enumerate(pts)}
    res=[]
    for st in sorted(out):
        p=[idx[ph[run_aut(st,inv_[y])]] for y in pts]
        res.append(is_mob(p,k,pts,lambda cc: idx[tuple(cc)]))
    print(k,res,flush=True)
