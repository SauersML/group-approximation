#!/usr/bin/env python3
"""Referee check (2026-09-16) of Lemma 3-prime in research/artifacts/berend-dual-circle-rokhlin-obstruction-2026-09-16.md:
for Gamma = <a, a+1> and random characters v of exact order p^j, the matrix-side stabilizer
{gamma : M_gamma^T v = v mod p^j} equals the ring-side Gamma cap (1 + p^j L). Single-threaded, seconds."""
import itertools, random
def mul(x,y,N):
    c=[0]*5
    for i in range(3):
        for j in range(3): c[i+j]+=x[i]*y[j]
    return ((c[0]+c[3]-c[4])%N,(c[1]+2*c[3]-c[4])%N,(c[2]-c[3]+3*c[4])%N)
def pw(x,e,N):
    r=(1,0,0)
    for _ in range(e): r=mul(r,x,N)
    return r
def matrix(g,N):  # columns g*1,g*a,g*a^2
    cols=[mul(g,(1,0,0),N),mul(g,(0,1,0),N),mul(g,(0,0,1),N)]
    return [[cols[k][i] for k in range(3)] for i in range(3)]
def fixes(g,v,N):
    # character chi_v(w)=exp(2 pi i v.w/N); gamma fixes iff v.(g w) = v.w for all w iff M^T v = v
    M=matrix(g,N)
    return all(sum(M[i][k]*v[i] for i in range(3))%N==v[k] for k in range(3))
random.seed(1)
for p,j,e in ((2,2,14),(2,3,28),(3,1,26),(3,2,78)):
    N=p**j
    elems=[(n,m) for n in range(e) for m in range(e)]
    ring=set((n,m) for n,m in elems if mul(pw((0,1,0),n,N),pw((1,1,0),m,N),N)==(1,0,0))
    vs=[v for v in itertools.product(range(N),repeat=3) if any(x%p for x in v)]
    bad=0
    for v in random.sample(vs,min(40,len(vs))):
        st=set((n,m) for n,m in elems if fixes(mul(pw((0,1,0),n,N),pw((1,1,0),m,N),N),v,N))
        if st!=ring: bad+=1
    print(p,j,"tested",min(40,len(vs)),"mismatches",bad,"|stab residues|",len(ring))
