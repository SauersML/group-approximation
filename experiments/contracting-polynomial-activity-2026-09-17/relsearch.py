"""Batch relation search: enumerate reduced words up to length L, group equal elements,
report pairs with different character value chi (chi given on states)."""
from autgrp import *
import sys
def relsearch(A, gens, chi, L, maxwords=3000000):
    U=Universe(A)
    words=[()]
    frontier=[()]
    for l in range(L):
        nf=[]
        for w in frontier:
            for g in gens:
                if w and A.inv[w[-1]]==g: continue
                nf.append(w+(g,))
        frontier=nf
        words+=nf
        if len(words)>maxwords: break
    for w in words: U.add(w)
    U.refine()
    seen={}
    bad=[]
    for w in words:
        c=U.cls[U.id[A.reduce(w)]]
        v=sum(chi[s] for s in w)
        if c in seen:
            w0,v0=seen[c]
            if abs(v-v0)>1e-9:
                bad.append((w0,w,v-v0))
        else:
            seen[c]=(w,v)
    return len(words), len(seen), bad
if __name__=="__main__":
    I=(0,1,2); R=(1,2,0); T12=(0,2,1); Rinv=(2,0,1)
    st=[(I,(0,0,0)), (R,(0,0,1)), (T12,(2,1,3)), (Rinv,(3,0,0))]
    A=fix_inverses(Automaton(3,st))
    chi={0:0,1:1,2:0,3:-1}
    for s in range(A.nstates): chi.setdefault(s,0)
    for L in range(4,int(sys.argv[1])+1,2):
        n,k,bad=relsearch(A,[1,2,3],chi,L)
        print(L,n,k,len(bad),bad[:3],flush=True)
