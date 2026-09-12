#!/usr/bin/env python3
"""Finite checks only: finite-priority deletion, local probabilities, and piece bounds.
No test below verifies an infinite group, a measurable theorem, or a universal conjecture.
"""
from __future__ import annotations
import argparse, itertools, json, math
from fractions import Fraction
from pathlib import Path

class DSU:
    def __init__(self,n): self.p=list(range(n))
    def find(self,a):
        while self.p[a]!=a:
            self.p[a]=self.p[self.p[a]]; a=self.p[a]
        return a
    def union(self,a,b):
        a,b=self.find(a),self.find(b)
        if a!=b:self.p[b]=a
    def relation(self):
        return tuple(tuple(self.find(i)==self.find(j) for j in range(len(self.p))) for i in range(len(self.p)))

def partitions(n):
    def rec(a):
        if len(a)==n:yield tuple(a);return
        for j in range(max(a)+2):yield from rec(a+[j])
    yield from rec([0])

def integral(lengths):
    coeff={0:1}
    for l in lengths:
        c=dict(coeff)
        for e,v in coeff.items():c[e+l]=c.get(e+l,0)-v
        coeff=c
    return sum((Fraction(v,e+1) for e,v in coeff.items()),Fraction())

def main():
    stats={}; assertions=0
    perms=list(itertools.permutations(range(3)))
    idx={p:i for i,p in enumerate(perms)}
    mul=[[idx[tuple(p[q[i]] for i in range(3))] for q in perms] for p in perms]
    e=idx[(0,1,2)]
    def powers(c):
        out=[];v=c
        while v!=e:out.append(v);v=mul[v][c]
        return out
    alist=[idx[(1,0,2)],idx[(1,2,0)]]
    parts=list(partitions(6));trials=0;deleted=0
    for a in alist:
        # Every b in the finite group provides a cycle when a*b != identity.
        cycles=[(b,powers(mul[a][b])) for b in range(6) if mul[a][b]!=e]
        for part in parts:
            base=DSU(6)
            for x in range(6):
                for y in range(x):
                    if part[x]==part[y]:base.union(x,y)
            full=DSU(6);full.p=base.p.copy()
            for x in range(6):full.union(x,mul[x][a])
            target=full.relation()
            # Admissible cycles may vary at each root and may overlap arbitrarily.
            supports=[]
            for x in range(6):
                local=[]
                for b,ps in cycles:
                    c=mul[a][b]; seq=[e]+ps
                    if all(part[mul[mul[x][v]][a]]==part[mul[x][mul[v][c]]] for v in seq):
                        local.append(tuple(mul[x][v] for v in ps))
                supports.append(local)
            ranks=itertools.product(range(2),repeat=6)
            for rank in ranks:
                kept=[not any(all(rank[y]<rank[x] for y in ps) for ps in supports[x]) for x in range(6)]
                out=DSU(6);out.p=base.p.copy()
                for x in range(6):
                    if kept[x]:out.union(x,mul[x][a])
                assert out.relation()==target
                assertions+=1;trials+=1;deleted+=sum(not t for t in kept)
    stats['finite_priority']={'group':'regular S3 action','partitions':len(parts),'generators_tested':len(alist),'binary_rank_assignments_per_case':64,'cases':trials,'deleted_edge_instances':deleted,'arbitrary_subrelations':True,'ties_included':True}
    # Additional all-distinct ranks on selected subrelations, exercising longer descents.
    extra=0
    for a in alist:
        for part in parts[::17]:
            base=DSU(6)
            for x in range(6):
                for y in range(x):
                    if part[x]==part[y]:base.union(x,y)
            full=DSU(6);full.p=base.p.copy()
            for x in range(6):full.union(x,mul[x][a])
            target=full.relation()
            supports=[]
            for x in range(6):
                local=[]
                for b in range(6):
                    c=mul[a][b]
                    if c==e:continue
                    ps=powers(c)
                    if all(part[mul[mul[x][v]][a]]==part[mul[x][mul[v][c]]] for v in [e]+ps):local.append(tuple(mul[x][v] for v in ps))
                supports.append(local)
            for rank in itertools.permutations(range(6)):
                out=DSU(6);out.p=base.p.copy()
                for x in range(6):
                    if not any(all(rank[y]<rank[x] for y in ps) for ps in supports[x]):out.union(x,mul[x][a])
                assert out.relation()==target;assertions+=1;extra+=1
    stats['distinct_priority_cases']=extra
    profiles=[(1,),(2,),(3,),(1,1),(1,2),(2,2),(1,1,2),(2,3),(1,2,3),(2,2,2)]
    permutation_cases=0
    for lengths in profiles:
        m=sum(lengths);supports=[];j=1
        for l in lengths:supports.append(tuple(range(j,j+l)));j+=l
        keep=0
        for rank in itertools.permutations(range(m+1)):
            keep+=not any(all(rank[z]<rank[0] for z in s) for s in supports)
            permutation_cases+=1
        assert Fraction(keep,math.factorial(m+1))==integral(lengths);assertions+=1
    for L in range(1,25):
        z=Fraction(1)
        for k in range(1,26):
            z*=Fraction(L*k,L*k+1)
            assert z==integral([L]*k);assertions+=1
    stats['integral_checks']={'profiles':len(profiles),'permutation_cases':permutation_cases,'beta_product_identities':24*25}
    # Exact priority upper bound in the prior odd Burnside calculation.
    def ceil_decimal(f,d=12):
        scale=10**d; n=(f.numerator*scale+f.denominator-1)//f.denominator
        return str(n//scale)+'.'+str(n%scale).zfill(d)
    bounds={}
    for n in [1003,10001]:
        L=n-1;z=Fraction(1)
        for j in range(1,n+1):z*=Fraction(L*j,L*j+1)
        v=1-Fraction(1,n)+z
        bounds[str(n)]={'outward_rounded_rational_upper':ceil_decimal(v),'formula':'1-1/n + product(j=1..n, (n-1)*j/((n-1)*j+1))'}
        assert v<2-Fraction(2,n);assertions+=1
    stats['rational_upper_bounds']=bounds
    # Proper-power symmetrized-set convention with nonprime exponents.
    rels=[]
    for i,n in enumerate([14,16,18,20,22,24,26,28],start=1):
        word='a'+'b'*i;r=word*n
        inv=''.join({'a':'A','b':'B'}[c] for c in r[::-1])
        for t in [r,inv]:
            for rot in range(i+1):rels.append((i,n,t[rot:]+t[:rot]))
    pair_tests=0
    for ix,(i,n,u) in enumerate(rels):
        for j,m,v in rels[ix+1:]:
            if u==v:continue
            l=0
            for x,y in zip(u,v):
                if x!=y:break
                l+=1
            assert l<=2*min(i,j)+1
            assert 6*l<min(len(u),len(v));assertions+=2;pair_tests+=1
    stats['composite_small_cancellation']={'profiles':[14,16,18,20,22,24,26,28],'distinct_symmetrized_words':len(rels),'pairs':pair_tests,'scope':'finite word-overlap checks only; no infinite-group intersection theorem checked'}
    stats['exact_assertions']=assertions
    stats['limitations']=['Finite checks do not verify infinite measurable selection or cost infima.','No test verifies the imported convex embedding and connected-intersection lemmas.','No universal conjecture is proved or certified.','No originality or independent-referee claim is made.']
    return stats

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);args=p.parse_args()
    data=main();args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(json.dumps(data,indent=2)+'\n');print(json.dumps(data,indent=2))
