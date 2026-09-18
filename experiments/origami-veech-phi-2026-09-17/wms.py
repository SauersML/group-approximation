from perm import *
# Q8 as pairs (sign, unit) unit in 1,i,j,k
units = ['1','i','j','k']
tab = {('1',u):(1,u) for u in units}
tab.update({(u,'1'):(1,u) for u in units})
for u in 'ijk': tab[(u,u)] = (-1,'1')
tab.update({('i','j'):(1,'k'),('j','i'):(-1,'k'),('j','k'):(1,'i'),('k','j'):(-1,'i'),('k','i'):(1,'j'),('i','k'):(-1,'j')})
els = [(s,u) for s in (1,-1) for u in units]
idx = {e:n for n,e in enumerate(els)}
def qm(a,b):
    s,u = tab[(a[1],b[1])]; return (a[0]*b[0]*s,u)
def left(g): return tuple(idx[qm(g,e)] for e in els)
B, C = left((1,'i')), left((1,'j'))
#print("rank [B,C]-I", perm_rank_defect(comm(B,C)))
Ts = list(isos((B,C),(B,mul(B,C)))); Ss = list(isos((B,C),(C,inv(B))))
#print(len(Ts), len(Ss))
best = None
for s in Ss:
    for t in Ts:
        R = relators(B,C,s,t)
        tot = {k:perm_rank_defect(v) for k,v in R.items()}
        if best is None or sum(tot.values()) < sum(best[0].values()): best = (tot,s,t)
#print(best)
#
#
#print(R['s^2(st)^-3'], R['[b,c]'], mul(R['s^2(st)^-3'],B)==mul(B,R['s^2(st)^-3']))
