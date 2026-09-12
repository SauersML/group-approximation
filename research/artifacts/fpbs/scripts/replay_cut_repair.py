#!/usr/bin/env python3
"""Finite checks for fractional-cut repair; does not verify infinite cost theorems."""
from __future__ import annotations
import argparse
import itertools as it
import json
from collections import Counter
from fractions import Fraction as F
from pathlib import Path

COUNTS: Counter[str] = Counter()

def check(condition: bool, name: str) -> None:
    if not condition:
        raise AssertionError(name)
    COUNTS[name] += 1


def subset_weight(mask: int, n: int, q: F) -> F:
    k = mask.bit_count()
    return q**k * (1-q)**(n-k)


def support_checks() -> dict:
    families = 0
    labels = 4
    for size in range(1, 5):
        for supports in it.combinations(range(1, 1 << labels), size):
            families += 1
            usage = [sum(bool(p & (1 << y)) for p in supports) for y in range(labels)]
            read = max(usage)
            # A second, nonuniform fractional packing, with denominator four.
            numer = [1] * size
            for e, p in enumerate(supports):
                while numer[e] < 4:
                    trial = numer.copy()
                    trial[e] += 1
                    if all(sum(trial[i] for i, s in enumerate(supports) if s & (1 << y)) <= 4
                           for y in range(labels)):
                        numer = trial
                    else:
                        break
            for y in range(labels):
                check(sum(numer[i] for i, p in enumerate(supports) if p & (1 << y)) <= 4,
                      'fractional_load_feasibility')
            for q in (F(1, 4), F(1, 2), F(3, 4)):
                failure = sum((subset_weight(mask, labels, q) for mask in range(1 << labels)
                               if all(mask & p != p for p in supports)), F(0))
                uniform_rhs = F(1)
                weighted_rhs = F(1)
                for i, p in enumerate(supports):
                    z = 1 - q**p.bit_count()
                    uniform_rhs *= z
                    weighted_rhs *= z**numer[i]
                # Integer powers make both inequalities exact rational comparisons.
                check(failure**read <= uniform_rhs, 'uniform_fractional_holder')
                check(failure**4 <= weighted_rhs, 'nonuniform_fractional_holder')
    return {'distinct_support_families': families, 'rational_q_values': ['1/4','1/2','3/4']}


def cuts(n: int, edges: list[tuple[int, int]], weights: tuple[F, ...]) -> list[F]:
    # Orient cuts by requiring vertex zero on the first side.
    vals = []
    for mask in range(1, (1 << n) - 1, 2):
        vals.append(sum((w for (u, v), w in zip(edges, weights)
                         if bool(mask & (1 << u)) != bool(mask & (1 << v))), F(0)))
    return vals


def cut_count_checks() -> dict:
    connected = 0
    for n in range(2, 6):
        edges = list(it.combinations(range(n), 2))
        choices = (F(0), F(1,2), F(3,2)) if n <= 4 else (F(0), F(1))
        for weights in it.product(choices, repeat=len(edges)):
            values = cuts(n, edges, weights)
            kappa = min(values)
            if kappa <= 0:
                continue
            connected += 1
            for j in (1,2,3,4):
                check(sum(v <= j*kappa for v in values) <= n**(2*j), 'weighted_cut_count')
    return {'connected_weighted_graphs': connected, 'max_vertices':5,
            'weights_up_to_four_vertices':['0','1/2','3/2'],
            'five_vertex_graphs':'all connected simple labelled graphs'}


def partitions(n: int):
    def extend(a: tuple[int, ...]):
        if len(a) == n:
            yield a
        else:
            for k in range(max(a) + 2):
                yield from extend(a + (k,))
    yield from extend((0,))


class DSU:
    def __init__(self, n: int):
        self.p = list(range(n))
    def root(self, x: int) -> int:
        while self.p[x] != x:
            self.p[x] = self.p[self.p[x]]
            x = self.p[x]
        return x
    def join(self, a: int, b: int) -> None:
        self.p[self.root(a)] = self.root(b)


def repair_checks() -> dict:
    partition_count = colorings = 0
    for n in range(2, 7):
        for part in partitions(n):
            partition_count += 1
            nodes = max(part)+1
            rows = []
            for mask in range(1 << n):
                colorings += 1
                d = DSU(nodes)
                for x in range(n):
                    if mask & (1 << x):
                        d.join(part[x], part[(x+1) % n])
                bad = [x for x in range(n) if d.root(part[x]) != d.root(part[(x+1) % n])]
                disconnected = len({d.root(v) for v in range(nodes)}) > 1
                check(F(len(bad), n) <= int(disconnected), 'root_failure_below_network_failure')
                for x in bad:
                    d.join(part[x], part[(x+1) % n])
                check(len({d.root(v) for v in range(nodes)}) == 1, 'paid_repair_connects')
                rows.append((mask, F(len(bad), n)))
            for q in (F(1,4), F(1,2), F(3,4)):
                selected_mean = sum((subset_weight(mask, n, q)*F(mask.bit_count(), n)
                                     for mask, _ in rows), F(0))
                check(selected_mean == q, 'mean_selected_domain_exact')
    return {'finite_subrelations':partition_count, 'exhaustive_colorings':colorings,
            'model':'regular cyclic action, all set partitions, sizes 2 through 6'}


def corridor_checks() -> dict:
    examples = 0
    for m in range(1,5):
        for w in range(1,4):
            if m*w > 10:
                continue
            examples += 1
            paths = list(it.product(range(w), repeat=m))
            for q in (F(1,4),F(1,2),F(3,4)):
                probability = sum((subset_weight(mask,m*w,q) for mask in range(1 << (m*w))
                    if all(any(mask & (1 << (j*w+k)) for k in range(w)) for j in range(m))),F(0))
                check(probability == (1-(1-q)**w)**m, 'corridor_reliability_exact')
                energy = sum((q**(-sum(a==b for a,b in zip(p,r)))
                              for p in paths for r in paths), F(0))/len(paths)**2
                formula = (1+(1/q-1)/w)**m
                check(energy == formula, 'corridor_overlap_energy_exact')
                check(1/energy <= probability, 'previous_second_moment_valid')
    # Algebraic identities only; these are not a finite model of a free F2 action.
    for den in range(2,31):
        for num in range(1,den):
            t=F(num,den)
            y=F(1,den)
            check((1+t)-1 == y*((1+t/y)-1), 'section_normalization_identity')
    return {'small_corridors':examples,
            'seed_checks':'rational normalization identities only, no verification of infinite treeings'}


def numerical_benchmarks() -> dict:
    import mpmath as mp
    mp.mp.dps=100
    rows=[]
    for j in (4,8,16,32,64):
        m=2**j; w=j*j; q=mp.mpf(2)/j
        fail_one=mp.exp(w*mp.log1p(-q))
        failure=-mp.expm1(m*mp.log1p(-fail_one))
        log_m=m*mp.log1p((1/q-1)/w)
        old_penalty=-mp.expm1(-log_m)
        rows.append({'j':j,'interfaces':str(m),'width':w,'q':str(q),
                     'actual_failure':mp.nstr(failure,24),
                     'paid_repair_bound':mp.nstr(q+failure,24),
                     'log_min_old_energy':mp.nstr(log_m,24),
                     'old_failure_upper_bound':mp.nstr(old_penalty,24)})
    # LP examples are numerical, separated from exact checks.
    import numpy as np
    from scipy.optimize import linprog
    lps=[]
    for m,w,shared in ((3,4,False),(3,4,True),(5,7,False)):
        edges=[(i,i+1) for i in range(m) for _ in range(w)]
        supports=[{e} if not shared else {0,e+1} for e in range(len(edges))]
        labels=sorted(set().union(*supports)); ne=len(edges)
        aub=[]; bub=[]
        for label in labels:
            aub.append([float(label in p) for p in supports]+[0.]); bub.append(1.)
        for mask in range(1,(1 << (m+1))-1,2):
            aub.append([-float(bool(mask&(1<<u)) != bool(mask&(1<<v))) for u,v in edges]+[1.])
            bub.append(0.)
        result=linprog([0.]*ne+[-1.],A_ub=np.asarray(aub),b_ub=np.asarray(bub),
                       bounds=[(0,None)]*(ne+1),method='highs')
        if not result.success:
            raise RuntimeError(result.message)
        expected=1/m if shared else w
        if abs(result.x[-1]-expected)>1e-8:
            raise AssertionError('LP benchmark mismatch')
        lps.append({'interfaces':m,'width':w,'shared_label_everywhere':shared,
                    'numerical_capacity':float(result.x[-1]),'analytic_capacity':str(F(1,m) if shared else F(w))})
    return {'method':'mpmath 100 decimal digits; scipy numerical LP; NOT exact assertions',
            'corridors':rows,'capacity_lps':lps}


def main() -> None:
    p=argparse.ArgumentParser()
    p.add_argument('--output',type=Path,required=True)
    args=p.parse_args()
    result={'scope':'finite combinatorics and arithmetic, not a proof of infinite cost statements',
            'support_tests':support_checks(), 'cut_tests':cut_count_checks(),
            'repair_tests':repair_checks(), 'corridor_tests':corridor_checks()}
    result['exact_assertions']=dict(COUNTS)
    result['exact_assertion_total']=sum(COUNTS.values())
    result['numerical_benchmarks']=numerical_benchmarks()
    result['status']='PASS'
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k !='numerical_benchmarks'},indent=2))

if __name__=='__main__':
    main()
