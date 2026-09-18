# For each cyclically reduced word, the elliptic cone E_w = {w in R^2: <w,m> >= 0 for all monomials m of charpoly}.
# A ray w (v(q),v(t)) is 'tropically hyperbolic for all words' iff it avoids every E_w.
import pickle, sys, math
res=pickle.load(open(sys.argv[1],'rb'))
def eig_vals(cp,w):
    # Newton polygon slopes -> eigenvalue valuations
    pts=[(k,min(w[0]*i+w[1]*j for (i,j) in cp[k])) for k in sorted(cp) if cp[k]]
    hull=[]
    for p in pts:
        while len(hull)>=2 and (hull[-1][1]-hull[-2][1])*(p[0]-hull[-2][0])>=(p[1]-hull[-2][1])*(hull[-1][0]-hull[-2][0]): hull.pop()
        hull.append(p)
    vals=[]
    for (k0,v0),(k1,v1) in zip(hull,hull[1:]):
        vals+= [-(v1-v0)/(k1-k0)]*(k1-k0)   # root valuations
    return sorted(vals)

M=720
ell={}
for s in range(M):
    th=2*math.pi*s/M; w=(math.cos(th),math.sin(th))
    bad=[x for x,cp in res.items() if max(abs(v) for v in eig_vals(cp,w))<1e-9]
    if bad: ell[s]=bad
print('rays(of %d) with an elliptic word:'%M, len(ell))
free=[s for s in range(M) if s not in ell]
# report intervals
def intervals(S):
    S=sorted(S); out=[]; 
    for s in S:
        if out and s==out[-1][1]+1: out[-1][1]=s
        else: out.append([s,s])
    return out
print('hyperbolic-for-all intervals (deg):',[(a/2,b/2) for a,b in intervals(free)])
for s in list(ell)[:0]: pass
import collections
cnt=collections.Counter(min(v,key=len) for v in ell.values())
print('shortest elliptic witnesses:',cnt.most_common(12))
for w in ['a','b','ab','aB','abAB']:
    if w in res: print(w,[eig_vals(res[w],(1,0)),eig_vals(res[w],(0,1)),eig_vals(res[w],(1,1))])
