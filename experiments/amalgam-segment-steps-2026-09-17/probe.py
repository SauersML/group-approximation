#!/usr/bin/env python3
"""Print, for each relator (a/b/A/B letters), the Magnus rewrites r' for every generator of
exponent sum 0 (after the certifier's Nielsen normalisation), the exponent vector e, the
number of occurrences of each letter a_i, and the integral window-lattice chain
Lambda_0 > Lambda_1 > ... (rows: a basis) of retract_segment_certify.lattice_chain.
Usage: probe.py WORD ..."""
import sys,os
sys.path.insert(0,os.path.join(os.path.dirname(os.path.abspath(__file__)),"..","perfect-kernel-segment-targets-2026-09-17"))
import retract_segment_certify as rsc
hc=rsc.hc; sc=rsc.sc
def P(s): return tuple((0 if c in "aA" else 1, 1 if c.islower() else -1) for c in s)
for s in sys.argv[1:]:
    w=P(s); w0=hc.canon(hc.cred(w)); w0=w0 if 0 in hc.exps(w0).values() else hc.nielsen_zero(w0); e=hc.exps(w0)
    print(s, "exps",e)
    for t in [a for a in e if e[a]==0]:
        r=hc.rewrite(w0,t); lo=min(p for (_,p),_ in r)
        rr=tuple(((0,p-lo),x) for (_,p),x in r)
        m=max(p for (_,p),_ in rr)
        ev=[0]*(m+1)
        for (_,p),x in rr: ev[p]+=x
        occ=[sum(1 for (_,p),_ in rr if p==i) for i in range(m+1)]
        print("  t=",t,"r'=",sc.show(rr),"e=",ev,"occ",occ, "chain",rsc.lattice_chain(ev))
