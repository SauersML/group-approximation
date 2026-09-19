import sys
sys.argv=['x']
from primes import *
def tagged(F):
    ed=edges_of(F); out=[]
    out += [('eb',e,fan_edge_blowup(F,e,ed)) for e in ed]
    out += [('fb',t,face_blowup(F,t)) for t in F]
    out += [('flop',f,do_flop(F,f)) for f in flops(F,ed)]
    out += [('bd',b,do_fan_blowdown(F,b)) for b in fan_blowdowns(F)]
    return out
start=frozenset([DELTA]); seen={canon(start)}; frontier=[start]
for depth in range(8):
    new=[]
    for F in frontier:
        for tag,arg,G in tagged(F):
            if len(G)>9: continue
            if sum(weight(t) for t in G)!=1:
                print("BAD move",tag,arg); print("parent",sorted(F)); print("child",sorted(G)); sys.exit(0)
            k=canon(G)
            if k not in seen: seen.add(k); new.append(G)
    frontier=new
print("no bad move found", len(seen))
