#!/usr/bin/env python3
"""Referee cross-check (2026-09-16), written independently of check_bs_rips.py.

Own Britton normal form for BS(m,n). For random staircase paths P (up to 40 per
group) it checks, at the vertex 1 only: |S| = 2+2(m+N); the link graph
(s ~ s2 iff s^-1 s2 in S) has exactly 3(m+N) edges, i.e. 3(m+N) triangles at 1,
as predicted by Lemmas C and D; and the link graph is triangle-free (no 4-clique,
Lemma E). Groups: BS(2,3), BS(3,-5), BS(5,2), BS(6,4), BS(1,7),
BS(5,-7), BS(4,6), BS(7,7), BS(6,-9), BS(2,-2), BS(3,1), BS(8,5). Mutation test at the end: non-staircase point sets must be rejected.
"""
import random, itertools, sys
def mk(m,n):
    N=abs(n)
    def mul(g, word):
        st=list(g[0]); j=g[1]
        for (gen,e) in word:
            if gen=='a': j+=e; continue
            if st and st[-1][1]==-e:
                if e==-1 and j%m==0:
                    r,_=st.pop(); j=r+(j//m)*n; continue
                if e==1 and j%N==0:
                    r,_=st.pop(); j=r+(j//n)*m; continue
            if e==1:
                r=j%N; q=(j-r)//n; st.append((r,1)); j=q*m
            else:
                r=j%m; q=(j-r)//m; st.append((r,-1)); j=q*n
        return (tuple(st),j)
    return mul
def inv(word): return [(g,-e) for (g,e) in reversed(word)]
def apow(k): return [('a',1)]*k if k>=0 else [('a',-1)]*(-k)
def run(m,n,P):
    N=abs(n); d=1 if n>0 else -1
    mul=mk(m,n); E=((),0)
    # sanity: relator
    assert mul(E,[('t',1)]+apow(m)+[('t',-1)]+apow(-n))==E
    words=[[('a',1)],[('a',-1)]]
    for (r,i) in P:
        w=apow(-d*i)+[('t',1)]+apow(r); words+= [w, inv(w)]
    elems={}
    for w in words: elems.setdefault(mul(E,w),w)
    assert E not in elems
    S=list(elems.items())
    assert len(S)==2+2*(m+N), (len(S),m,n)
    Sset=set(elems)
    adj={s:set() for s in Sset}
    for s,ws in S:
        for s2,w2 in S:
            if s!=s2 and mul(E, inv(ws)+w2) in Sset: adj[s].add(s2)
    ne=sum(len(v) for v in adj.values())//2
    assert ne==3*(m+N),(ne,m,n,P)
    for s in Sset:
        for s2 in adj[s]:
            assert not (adj[s]&adj[s2]), "4-clique"
    return True
def paths(m,N):
    for comb in itertools.combinations(range(m+N),m):
        p=[(0,0)];r=i=0
        for k in range(m+N):
            if k in comb: r+=1
            else: i+=1
            p.append((r,i))
        yield p
random.seed(7); cnt=0
for m,n in [(2,3),(3,-5),(5,2),(6,4),(1,7),(5,-7),(4,6),(7,7),(6,-9),(2,-2),(3,1),(8,5)]:
    N=abs(n); ps=list(paths(m,N)); random.shuffle(ps)
    for P in ps[:40]:
        run(m,n,P); cnt+=1
print("staircase sets checked:",cnt)

if __name__ == "__main__":
    for m,n,P in [(2,3,[(0,0),(1,0),(1,1),(1,2),(2,3)]),(2,3,[(0,0),(1,0),(0,1),(1,2),(2,2),(2,3)])]:
        try:
            run(m,n,P); print("MUTANT ACCEPTED (bad)",m,n,P)
        except AssertionError:
            print("mutant rejected",m,n,P)
