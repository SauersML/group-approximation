#!/usr/bin/env python3
"""Exact finite checks for arbitrary-subrelation torsion repair and phase sections.

These checks concern finite combinatorics and measure normalization.  They do not
prove aperiodic marker existence, any infinite cost theorem, or Fixed Price.
Only the Python standard library is used.
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction as F
from itertools import product, combinations
import json
from pathlib import Path
import random


def partitions(n: int):
    """All partitions as restricted-growth tuples, once each."""
    if n == 0:
        yield ()
        return
    a = [0] * n
    def rec(i: int, maximum: int):
        if i == n:
            yield tuple(a)
            return
        for v in range(maximum + 2):
            a[i] = v
            yield from rec(i + 1, max(maximum, v))
    yield from rec(1, 0)


class DSU:
    def __init__(self, n: int):
        self.p = list(range(n))
    def find(self, x: int) -> int:
        while self.p[x] != x:
            self.p[x] = self.p[self.p[x]]
            x = self.p[x]
        return x
    def union(self, x: int, y: int) -> None:
        self.p[self.find(x)] = self.find(y)


def seed_relation(labs: tuple[int, ...]) -> DSU:
    d = DSU(len(labs)); representatives = {}
    for x, lab in enumerate(labs):
        if lab in representatives:
            d.union(x, representatives[lab])
        else:
            representatives[lab] = x
    return d


def add_group(moduli: tuple[int, ...]):
    elems = list(product(*(range(p) for p in moduli)))
    idx = {g: i for i, g in enumerate(elems)}
    def mul(x: int, y: int) -> int:
        return idx[tuple((a+b) % p for a,b,p in zip(elems[x], elems[y], moduli))]
    def inv(x: int) -> int:
        return idx[tuple((-a) % p for a,p in zip(elems[x], moduli))]
    def order(x: int) -> int:
        z = 0
        for k in range(1, len(elems)+1):
            z = mul(z, x)
            if z == 0:
                return k
        raise AssertionError('finite group order failure')
    return elems, idx, mul, inv, order


def check_torsion():
    stats = Counter()
    rng = random.Random(20260909)
    for moduli, a_tuple, c_tuples in [
        ((2,2), (1,0), [(1,0),(1,1)]),
        ((6,), (1,), [(3,),(2,)]),
        ((3,3), (1,0), [(1,0),(1,1),(1,2)]),
    ]:
        elems, idx, mul, inv, order = add_group(moduli)
        size = len(elems); a = idx[a_tuple]
        cs = [idx[c] for c in c_tuples]
        bs = [mul(inv(a),c) for c in cs]
        ds = [order(c) for c in cs]
        power_sets = []
        power_rows = []
        for c, di in zip(cs,ds):
            powers = [0]
            for j in range(di):
                powers.append(mul(powers[-1],c))
            assert powers[-1] == 0
            power_sets.append(set(powers[1:-1]))
            power_rows.append(powers)
        assert sum(map(len,power_sets)) == len(set().union(*power_sets))
        for a0 in range(len(power_sets)):
            assert len(power_sets[a0]) == ds[a0]-1
        if size <= 6:
            plist = list(partitions(size))
        else:
            plist = [tuple(range(size)), (0,)*size]
            for _ in range(12):
                raw=[rng.randrange(rng.randrange(1,size+1)) for __ in range(size)]
                canon={}; labs=[]
                for v in raw:
                    canon.setdefault(v,len(canon)); labs.append(canon[v])
                plist.append(tuple(labs))
            for coord in (0,1):
                plist.append(tuple(g[coord] for g in elems))
            plist = sorted(set(plist))
        for labs in plist:
            stats['arbitrary_subrelations'] += 1
            admissible=[]
            for x in range(size):
                row=[]
                for b,di,powers in zip(bs,ds,power_rows):
                    good=True
                    for j in range(di):
                        u=mul(mul(x,powers[j]),a)
                        v=mul(x,powers[j+1])
                        assert mul(u,b)==v
                        if labs[u]!=labs[v]:
                            good=False
                    row.append(good)
                admissible.append(row)
            for i,(b,di) in enumerate(zip(bs,ds)):
                failure=sum(not row[i] for row in admissible)
                defect=sum(labs[x]!=labs[mul(x,b)] for x in range(size))
                assert failure <= di*defect
                stats['union_bound_identities'] += 1
            for q in (F(1,3), F(2,5)):
                expected_total=F(0)
                expected_failed=F(0)
                for mask in range(1<<size):
                    selected=[bool(mask & (1<<x)) for x in range(size)]
                    failure=[]
                    for x in range(size):
                        successful=False
                        for i,powers in enumerate(power_rows):
                            if admissible[x][i] and all(selected[mul(x,z)] for z in powers[1:-1]):
                                successful=True; break
                        failure.append(not successful)
                    dd=seed_relation(labs)
                    for x in range(size):
                        if selected[x] or failure[x]:
                            dd.union(x,mul(x,a))
                    assert all(dd.find(x)==dd.find(mul(x,a)) for x in range(size))
                    stats['repaired_coloring_cases'] += 1
                    nsel=sum(selected)
                    wt=q**nsel*(1-q)**(size-nsel)
                    expected_total += wt * F(nsel+sum(failure),size)
                    expected_failed += wt * F(sum(failure),size)
                rhs_fail=F(0)
                for row in admissible:
                    term=F(1)
                    for i,good in enumerate(row):
                        if good:
                            term *= 1-q**(ds[i]-1)
                    rhs_fail += term/size
                assert expected_failed == rhs_fail
                assert expected_total == q + rhs_fail
                stats['exact_product_expectations'] += 1
    return dict(stats)


def check_finite_index_stars():
    stats=Counter()
    for n in range(1,8):
        for labs in partitions(n):
            k=max(labs)+1
            reps={j:labs.index(j) for j in range(k)}
            for mask in range(1,1<<n):
                anchors=[x for x in range(n) if mask & (1<<x)]
                d=seed_relation(labs); edges=set()
                for x in anchors:
                    for j in range(k):
                        if j != labs[x]:
                            y=reps[j]
                            edges.add(tuple(sorted((x,y)))); d.union(x,y)
                assert len({d.find(x) for x in range(n)})==1
                assert len(edges) <= (k-1)*len(anchors)
                stats['star_completion_cases'] += 1
    return dict(stats)


def check_phase_sections():
    stats=Counter()
    for L,q in [(2,2),(3,3),(4,2),(6,2),(6,3)]:
        assert L%q==0
        # Z/L acts regularly on the base and by addition mod q on the phase.
        # Its lifted orbits are labeled j-x modulo q.
        c_beta=1-F(1,L)
        for labels in product(range(q),repeat=L):
            corrected=[(labels[x]-x)%q for x in range(L)]
            distinct=len(set(corrected))
            complete=(distinct==q)
            stats['phase_colorings'] += 1
            c_kernel=1-F(distinct,L)
            if complete:
                assert c_kernel-1 == q*(c_beta-1)
                stats['complete_single_phase_sections'] += 1
            else:
                # Deliberately do not apply complete-section induction here.
                stats['noncomplete_sections_excluded'] += 1
        for k in range(1,q+1):
            options=list(combinations(range(q),k))
            for rows in product(options,repeat=L):
                points=[(x,j) for x,row in enumerate(rows) for j in row]
                classes={(j-x)%q for x,j in points}
                if len(classes)!=q:
                    continue
                measure=F(len(points),L*q)
                c_section=1-F(q,len(points))
                assert c_beta-1 == measure*(c_section-1)
                assert c_section==1+F(q,k)*(c_beta-1)
                stats['complete_multiphase_sections'] += 1
    # Variable multiplicity, including empty fibers, in a small cyclic model.
    L,q=3,3
    options=[tuple(j for j in range(q) if mask & (1<<j)) for mask in range(1<<q)]
    for rows in product(options,repeat=L):
        points=[(x,j) for x,row in enumerate(rows) for j in row]
        if not points or len({(j-x)%q for x,j in points}) != q:
            continue
        m=F(len(points),L)
        c_beta=1-F(1,L)
        c_section=1-F(q,len(points))
        assert c_section==1+F(q,1)*(c_beta-1)/m
        stats['variable_multiplicity_sections']+=1
    return dict(stats)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path('phase-repair-checks.json'))
    args=parser.parse_args()
    out={
        'status':'passed',
        'scope':'Exact finite combinatorics and rational expectation/normalization identities only.',
        'not_verified':['aperiodic marker existence','infinite graphing cost','Burnside embedding theorems',
                        'Bernoulli spectral gap','Fixed Price','Benjamini-Schramm'],
        'arbitrary_subrelation_torsion_repair':check_torsion(),
        'finite_index_stars':check_finite_index_stars(),
        'finite_phase_sections':check_phase_sections(),
    }
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))

if __name__=='__main__':
    main()
