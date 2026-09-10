#!/usr/bin/env python3
"""Finite checks for the sparse-torsion/small-cancellation construction.

This is not a group-theorem prover. It checks finite word combinatorics and
finite paid-repair identities. No finite truncation certifies an infinite group.
"""
from __future__ import annotations
import argparse
import hashlib
import itertools
import json
from collections import Counter, deque
from fractions import Fraction
from pathlib import Path

COUNTS: Counter[str] = Counter()

def check(test: bool, family: str) -> None:
    if not test:
        raise AssertionError(f"Failed finite check: {family}")
    COUNTS[family] += 1

INV = str.maketrans('abAB', 'ABab')

def inverse(word: str) -> str:
    return word.translate(INV)[::-1]

def lcp(a: str, b: str) -> int:
    for i, (x,y) in enumerate(zip(a,b)):
        if x != y:
            return i
    return min(len(a),len(b))

def symmetrized(profile: list[int], start: int = 1):
    entries = {}
    for i,p in enumerate(profile, start):
        r = ('a'+'b'*i)*p
        # A proper-power period produces identical rotations. Those are NOT
        # different words in the symmetrized relator set.
        for s in (r,inverse(r)):
            for k in range(len(s)):
                v = s[k:]+s[:k]
                if v in entries:
                    check(entries[v] == i, 'rotation_deduplication')
                entries[v] = i
    return [(s,i) for s,i in sorted(entries.items())]

def piece_checks():
    profiles = [([13]*10,1), ([13,17]*5,1),
                ([13,17,19,23,29,31,37,41,43,47],1),
                ([13,17,19,23,29],20)]
    summaries=[]
    for profile,start in profiles:
        entries=symmetrized(profile,start)
        maximum=0
        for (s,i),(t,j) in itertools.combinations(entries,2):
            k=lcp(s,t)
            check(6*k < min(len(s),len(t)), 'C_prime_one_sixth_pairs')
            check(k <= 2*min(i,j)+1, 'piece_length_bound')
            maximum=max(maximum,k)
        summaries.append({'first_index':start,'primes':profile,
                          'distinct_symmetrized_words':len(entries),
                          'largest_piece_seen':maximum})
    return summaries

def free_subgroup_checks():
    entries=symmetrized([13,17,19,23,29],1)
    forbidden={s[:len(s)//2+1] for s,_ in entries}
    alphabet='xXyY'; inv={'x':'X','X':'x','y':'Y','Y':'y'}
    expansion={'x':'aa','X':'AA','y':'bb','Y':'BB'}
    frontier=['']
    tested=0
    for length in range(1,9):
        frontier=[w+c for w in frontier for c in alphabet
                  if not w or c != inv[w[-1]]]
        for w in frontier:
            if w[-1]==inv[w[0]]:
                continue
            v=''.join(expansion[c] for c in w)
            check(all(v[i+1] != inverse(v[i]) for i in range(len(v)-1)),
                  'free_subgroup_expansion_reduced')
            doubled=v+v
            check(not any(len(f)<=len(v) and f in doubled
                          for f in forbidden), 'free_subgroup_no_half_relator')
            tested+=1
    # Long deterministic words make this more than just a length cutoff test.
    for k in range(1,101):
        v='aa'+'b'*(2*k)+'AA'+'B'*(2*k)+'aa'+'bb'
        check(not any(len(f)<=len(v) and f in v+v for f in forbidden),
              'long_even_run_no_half_relator')
    return {'cyclically_reduced_words_in_two_squared_generators':tested,
            'additional_long_even_run_words':100,
            'relator_indices_checked':list(range(1,6))}

def omitted_relator_checks():
    # Test powers of omitted roots against all *other* finite relator words.
    entries=symmetrized([13,17,19,23,29,31,37],1)
    total=0
    for j in range(1,8):
        other=[s[:len(s)//2+1] for s,i in entries if i!=j]
        for power in (1,2,3,13,31,100):
            w=('a'+'b'*j)*power
            check(not any(len(f)<=len(w) and f in w+w for f in other),
                  'omitted_root_no_half_relator')
            total+=1
    return {'omitted_index_and_power_cases':total}

def dihedral_checks():
    # D_{2m}: (k,t)(l,u)=(k+(-1)^t*l mod m, t+u mod2).
    # a=(0,1), b=(1,0); c_i=a*b^i are distinct involutions.
    output=[]
    for m in range(3,7):
        group=[(k,t) for k in range(m) for t in range(2)]
        index={g:i for i,g in enumerate(group)}
        def mul(g,h):return ((g[0]+(-1 if g[1] else 1)*h[0])%m,(g[1]+h[1])%2)
        a=(0,1); b=(1,0)
        cs=[mul(a,(i,0)) for i in range(m)]
        check(len(set(cs))==m,'dihedral_disjoint_cycle_supports')
        for c in cs:check(mul(c,c)==(0,0),'dihedral_cycle_relations')
        totals={q:Fraction(0) for q in (Fraction(1,3),Fraction(1,2),Fraction(2,3))}
        for mask in range(1<<len(group)):
            U={g for j,g in enumerate(group) if mask>>j&1}
            D={x for x in group if all(mul(x,c) not in U for c in cs)}
            A=U|D
            adjacency={x:set() for x in group}
            for x in group:
                y=mul(x,b); adjacency[x].add(y);adjacency[y].add(x)
            for x in A:
                y=mul(x,a); adjacency[x].add(y);adjacency[y].add(x)
            reached={group[0]};todo=[group[0]]
            while todo:
                x=todo.pop()
                for y in adjacency[x]-reached:reached.add(y);todo.append(y)
            check(len(reached)==len(group),'paid_repair_connected_labelings')
            selected=len(U)
            for q in totals:
                mass=q**selected*(1-q)**(len(group)-selected)
                totals[q]+=mass*Fraction(len(A),len(group))
        for q,value in totals.items():
            expected=q+(1-q)*(1-q)**m
            check(value==expected,'union_probability_exact')
        output.append({'dihedral_order':len(group),'labelings':1<<len(group),
                       'probabilities':[str(q) for q in totals]})
    return output

def probability_profiles():
    profiles=[(1,1),(2,3),(2,2,3),(1,2,3,4),(3,3,3)]
    qvalues=(Fraction(1,3),Fraction(1,2),Fraction(2,3))
    for lengths in profiles:
        size=1+sum(lengths)
        success_sum={q:Fraction(0) for q in qvalues}
        supports=[];i=1
        for ell in lengths:supports.append(list(range(i,i+ell)));i+=ell
        for mask in range(1<<size):
            selected=bool(mask&1)
            failed=not any(all(mask>>j&1 for j in support) for support in supports)
            retained=selected or failed
            ones=mask.bit_count()
            for q in qvalues:
                if retained:success_sum[q]+=q**ones*(1-q)**(size-ones)
        for q in qvalues:
            product=Fraction(1)
            for ell in lengths:product*=1-q**ell
            check(success_sum[q]==q+(1-q)*product,'variable_length_union_probability')
    return {'support_length_profiles':[list(x) for x in profiles],
            'rational_probabilities':[str(q) for q in qvalues]}

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--output',type=Path,
        default=Path('research/artifacts/small-cancellation-checks.json'))
    args=parser.parse_args()
    result={
      'scope':'Finite word, probability, and repair checks only; not formal theorem verification.',
      'piece_profiles':piece_checks(),
      'free_subgroup_tests':free_subgroup_checks(),
      'omitted_relator_tests':omitted_relator_checks(),
      'finite_regular_actions':dihedral_checks(),
      'variable_length_probabilities':probability_profiles(),
      'assertions_by_family':dict(COUNTS),
      'total_assertions':sum(COUNTS.values()),
      'all_passed':True,
      'not_verified':['Greendlinger lemma','infinite presentation algebra',
        'measurable selection and infinite cost infima','acylindrical hyperbolicity theorem',
        'Choi-Seo percolation theorem','novelty or priority','either universal conjecture']}
    result['script_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
