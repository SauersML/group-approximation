#!/usr/bin/env python3
"""Exact finite checks for adaptive repair and finite-relation coefficients.
No infinite group theorem or measurable existence result is verified here.
"""
from __future__ import annotations
from fractions import Fraction as F
from itertools import combinations, permutations, product
from pathlib import Path
import argparse, json


def partitions(n: int):
    a = [0] * n
    def rec(i: int, mx: int):
        if i == n:
            yield tuple(a)
            return
        for v in range(mx + 2):
            a[i] = v
            yield from rec(i + 1, max(mx, v))
    yield from rec(1, 0)


def prob_of_mask(mask: int, n: int, q: F) -> F:
    k = mask.bit_count()
    return q ** k * (1-q) ** (n-k)


def overlap_checks():
    supports = [frozenset(i for i in range(4) if mask >> i & 1)
                for mask in range(1, 16)]
    counts = dict(families=0, probability_cases=0, moment_entries=0,
                  paley_zygmund_bounds=0, optimized_disjoint_cases=0,
                  common_bottleneck_cases=0)
    for k in (1, 2, 3):
        for fam in combinations(supports, k):
            counts['families'] += 1
            for q in (F(1,3), F(1,2), F(2,3)):
                counts['probability_cases'] += 1
                masks = [sum(1 << j for j in s) for s in fam]
                weights = [F(i+1, k*(k+1)//2) for i in range(k)]
                mean = F(0); second = F(0); fail = F(0)
                for m in range(16):
                    pr = prob_of_mask(m,4,q)
                    z = [F(int(m & s == s),1) / q ** len(fam[i])
                         for i,s in enumerate(masks)]
                    w = sum((weights[i]*z[i] for i in range(k)), F(0))
                    mean += pr*w; second += pr*w*w
                    if not any(z): fail += pr
                matrix_second = sum((weights[i]*weights[j]*q**(-len(fam[i]&fam[j]))
                                     for i in range(k) for j in range(k)), F(0))
                assert mean == 1 and second == matrix_second
                assert fail <= 1-1/second
                counts['paley_zygmund_bounds'] += 1
                counts['moment_entries'] += k*k
    for lens in [(1,), (1,2), (2,2,3), (1,3,5,7)]:
        for q in (F(1,4),F(1,3),F(1,2),F(2,3)):
            invs = [1/(q**(-l)-1) for l in lens]
            total = sum(invs,F(0)); weights=[z/total for z in invs]
            e = 1+sum((w*w*(q**(-l)-1) for w,l in zip(weights,lens)),F(0))
            assert e == 1+1/total
            assert 1-1/e == 1/(1+total)
            counts['optimized_disjoint_cases'] += 1
    for k in range(1,12):
        for q in (F(1,4),F(1,2),F(3,4)):
            e = 1/q+(1/(q*q)-1/q)/k
            fail = 1-q*(1-(1-q)**k)
            assert fail <= 1-1/e
            counts['common_bottleneck_cases'] += 1
    return counts


def finite_action_checks():
    els=list(permutations(range(3))); n=len(els)
    idx={g:i for i,g in enumerate(els)}
    mul=[[idx[tuple(g[h[t]] for t in range(3))] for h in els] for g in els]
    ident=idx[(0,1,2)]
    inv=[next(j for j in range(n) if mul[i][j]==ident) for i in range(n)]
    cycles=[]
    for c in range(n):
        arr=[]; z=c
        while z != ident:
            arr.append(z); z=mul[z][c]
        cycles.append(arr)
    counts=dict(partitions=0, coefficient_cases=0, defect_subadditivity=0,
                restriction_defect_cases=0, adaptive_root_families=0,
                repaired_labelings=0, root_energy_bounds=0,
                expected_cost_bounds=0)
    for part in partitions(n):
        counts['partitions'] += 1
        blocks=[frozenset(y for y in range(n) if part[y]==part[x]) for x in range(n)]
        defects=[]
        for g in range(n):
            phi=F(sum(part[x]==part[mul[x][g]] for x in range(n)),n)
            coeff=F(0)
            for x in range(n):
                xg=mul[x][g]
                left=frozenset(h for h in range(n) if mul[x][h] in blocks[x])
                right=frozenset(h for h in range(n) if mul[x][h] in blocks[xg])
                overlap=len(left & right)
                if overlap:
                    assert len(blocks[x])==len(blocks[xg])
                    coeff += F(overlap,len(blocks[x])*n)
            assert coeff == phi
            defects.append(1-phi); counts['coefficient_cases'] += 1
        for g in range(n):
            assert defects[g]==defects[inv[g]]
            for h in range(n):
                assert defects[mul[g][h]] <= defects[g]+defects[h]
                counts['defect_subadditivity'] += 1
        # Restrict to Y, then put singleton classes on its complement.
        for ymask in range(1<<n):
            delta=F(n-ymask.bit_count(),n)
            for g in range(n):
                ok=0
                for x in range(n):
                    y=mul[x][g]
                    if x==y or ((ymask>>x&1) and (ymask>>y&1) and part[x]==part[y]):
                        ok+=1
                defect_e=1-F(ok,n)
                assert defect_e <= defects[g]+2*delta
                counts['restriction_defect_cases'] += 1
        for a in range(n):
            if a==ident: continue
            # Families depend on the root and on the arbitrary subrelation.
            families=[]
            energies=[]
            for x in range(n):
                fam=[]
                if part[x]==part[mul[x][a]]:
                    fam.append(0)  # Already connected; empty support.
                for c in range(n):
                    if c==ident: continue
                    b=mul[inv[a]][c]
                    powers=[ident]+cycles[c]
                    good=True
                    for z in powers:
                        left=mul[mul[x][z]][a]
                        right=mul[mul[x][z]][c]
                        if part[left] != part[right]:
                            good=False; break
                    if good:
                        support=sum(1 << mul[x][z] for z in cycles[c])
                        fam.append(support)
                # A direct a edge always provides a valid fallback certificate.
                fam.append(1<<x)
                fam=list(dict.fromkeys(fam))
                families.append(fam)
                k=len(fam)
                e=F(sum(2**((p&r).bit_count()) for p in fam for r in fam),k*k)
                energies.append(e); counts['adaptive_root_families'] += 1
            failure_counts=[0]*n
            total_upper=F(0)
            for selected in range(1<<n):
                fail=0
                for x,fam in enumerate(families):
                    if not any(selected & p == p for p in fam):
                        fail |= 1<<x; failure_counts[x]+=1
                domain=selected|fail
                # Explicit connectivity after the selected edges and repair.
                adj=[set(blocks[x]) for x in range(n)]
                for x in range(n):
                    if domain>>x&1:
                        y=mul[x][a]; adj[x].add(y); adj[y].add(x)
                for x in range(n):
                    seen={x}; todo=[x]
                    while todo:
                        y=todo.pop()
                        for z in adj[y]-seen:
                            seen.add(z); todo.append(z)
                    assert mul[x][a] in seen
                total_upper += F(selected.bit_count()+fail.bit_count(),n*(1<<n))
                counts['repaired_labelings'] += 1
            bound=F(1,2)
            for x,e in enumerate(energies):
                failprob=F(failure_counts[x],1<<n)
                assert failprob <= 1-1/e
                bound += (1-1/e)/n
                counts['root_energy_bounds'] += 1
            assert total_upper <= bound
            counts['expected_cost_bounds'] += 1
    return counts


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    result={
      'status':'passed',
      'scope':'Exact finite rational identities and finite repaired connectivity only.',
      'overlap_matrix':overlap_checks(),
      'finite_S3_action':finite_action_checks(),
      'not_verified':['measurable partition separation in infinite actions',
                      'hyperfinite exhaustion and regular representation limits',
                      'Osin bounded-word theorem and Burnside nonamenability',
                      'the new infinite mathematical deductions',
                      'existence of the low-cost capacity witnesses',
                      'universal Fixed Price and Benjamini-Schramm']
    }
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__': main()
