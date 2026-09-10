#!/usr/bin/env python3
"""Exact finite tests for the torsion-detour argument, NOT infinite theorem verification.

Uses A5 only as a finite test fixture. It does not test the hypothesis that
arbitrarily many independent detours exist in an infinite coset, weak
containment, cost infima, or either universal conjecture.
"""
from __future__ import annotations
import argparse
from collections import Counter, deque
from fractions import Fraction
from itertools import permutations
import json
from pathlib import Path

Perm = tuple[int, ...]
ID: Perm = tuple(range(5))
def mul(a: Perm, b: Perm) -> Perm:
    return tuple(a[b[i]] for i in range(5))
def parity(a: Perm) -> int:
    return sum(a[i] > a[j] for i in range(5) for j in range(i + 1, 5)) % 2
def cyclic(a: Perm) -> list[Perm]:
    out: list[Perm] = []
    x = a
    while x != ID:
        out.append(x)
        x = mul(x, a)
        if len(out) > 60:
            raise AssertionError('Invalid finite-group order')
    return out

def reachable(adj: dict[Perm, set[Perm]], start: Perm) -> set[Perm]:
    seen = {start}
    todo = deque([start])
    while todo:
        x = todo.popleft()
        for y in adj[x]:
            if y not in seen:
                seen.add(y); todo.append(y)
    return seen

def run() -> dict:
    counts: Counter[str] = Counter()
    G = [a for a in permutations(range(5)) if not parity(a)]
    Gset = set(G)
    assert len(G) == 60
    centralizers = {a: {b for b in G if mul(a,b)==mul(b,a)} for a in G if a!=ID}
    for C in centralizers.values():
        assert all(mul(a,b)==mul(b,a) for a in C for b in C)
        counts['centralizers_abelian'] += 1
    for C in centralizers.values():
        for D in centralizers.values():
            assert C == D or C & D == {ID}
            counts['centralizer_intersections'] += 1
    # A4 fixing point 4. It is finite: the infinite-coset theorem is not tested.
    H = {a for a in G if a[4] == 4}
    assert len(H) == 12
    for a in Gset - H:
        for b in H:
            c = mul(a,b)
            powers = cyclic(c)
            assert powers and len(powers) <= 4
            assert all(g in Gset for g in powers)
            # e -> a is the omitted edge. Travel from a back to e instead.
            x = a
            x = mul(x,b)
            assert x == c
            for ell, power in enumerate(powers):
                assert x == power
                x = mul(x,a)     # available restricted a-edge at this power
                x = mul(x,b)     # H-edge, supplied by the H orbit relation
                expected = powers[ell+1] if ell+1 < len(powers) else ID
                assert x == expected
            assert x == ID
            counts['torsion_detour_identities'] += 1
    # Three disjoint power supports for one explicitly selected missing edge.
    a = min(Gset - H)
    supports: list[set[Perm]] = []
    used: set[Perm] = set()
    for b in sorted(H):
        P = set(cyclic(mul(a,b)))
        if not P & used:
            supports.append(P); used |= P
        if len(supports) == 3:
            break
    assert len(supports)==3
    coordinates = sorted(used)
    M = len(coordinates)
    base = {g: {mul(g,h) for h in H if h!=ID} for g in G}
    q_values = [Fraction(1,4), Fraction(1,3), Fraction(1,2), Fraction(2,3)]
    failure_sums = {q: Fraction(0) for q in q_values}
    success_count = 0
    for mask in range(1 << M):
        A = {g for i,g in enumerate(coordinates) if mask >> i & 1}
        success = any(P <= A for P in supports)
        adj = {g: set(ns) for g,ns in base.items()}
        for g in A:
            h = mul(g,a); adj[g].add(h); adj[h].add(g)
        if success:
            assert a in reachable(adj,ID)
            success_count += 1
        else:
            # The fallback adds the missing edge itself.
            adj[ID].add(a); adj[a].add(ID)
            assert a in reachable(adj,ID)
        for q in q_values:
            weight = q**len(A) * (1-q)**(M-len(A))
            if not success:
                failure_sums[q] += weight
        counts['selection_and_fallback_configurations'] += 1
    for q,total in failure_sums.items():
        exact = Fraction(1)
        for P in supports: exact *= 1 - q**len(P)
        assert total == exact
        assert total <= (1-q**4)**len(supports)
        counts['failure_probability_products'] += 1
        counts['bounded_order_failure_bounds'] += 1
    # Verify normalization of induced-action cost, including finite classes.
    # A single H-class of size h induces a class of size d*h.
    for h in range(1,21):
        for d in range(1,21):
            source = 1 - Fraction(1,h)
            induced = 1 + (source-1)/d
            assert induced == 1 - Fraction(1,d*h)
            counts['induction_normalization_checks'] += 1
    for n in range(3,60,2):
        for j in range(11):
            c = 1 + Fraction(j,10)*(1-Fraction(2,n))
            d = 1 + (c-1)/n
            assert c-d == (1-Fraction(1,n))*(c-1)
            assert 1 <= d <= 1+Fraction(1,n)-Fraction(2,n*n)
            counts['candidate_pair_algebra_checks'] += 1
    return {
        'status':'PASS',
        'scope':'Finite exact algebra and probability tests only; not a proof assistant.',
        'fixture':{'group':'A5','order':60,'H_order':len(H),'a':list(a),
                   'support_sizes':[len(P) for P in supports],
                   'label_coordinates':M,'successful_configurations':success_count},
        'checks_by_kind':dict(counts),
        'total_checked_cases':sum(counts.values()),
        'not_verified':[
            'Existence of arbitrarily many disjoint detours in infinite groups',
            'Abért-Weiss finite-pattern approximation on arbitrary free actions',
            'Infinite measured equivalence relations and cost infima',
            'Burnside centralizer and subgroup embedding theorems',
            'Whether the Burnside upper cost c_n equals one',
            'Either universal Fixed Price or Benjamini-Schramm conjecture'
        ]
    }

def main() -> None:
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path,default=Path(__file__).resolve().parents[1]/'research/artifacts/torsion-replay.json')
    args=ap.parse_args()
    result=run()
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result,indent=2))
if __name__=='__main__': main()
