#!/usr/bin/env python3
"""Exact FINITE checks supporting the torsion-free construction.
These checks do not prove the infinite-group or measurable assertions.
Run: python verify.py --output checks.json
Only Python's standard library is required.
"""
from __future__ import annotations
import argparse
import itertools
import json
import time
from collections import Counter
from fractions import Fraction
from pathlib import Path
from math import factorial

COUNTS: Counter[str] = Counter()

def check(condition: bool, category: str) -> None:
    if not condition:
        raise AssertionError(category)
    COUNTS[category] += 1

def bpower(exponent: int) -> str:
    return ('b' if exponent >= 0 else 'B') * abs(exponent)

def relator(i: int) -> str:
    return ''.join('a' + bpower(100*i+j) for j in range(1, 14))

def reduce_word(word: str) -> str:
    stack: list[str] = []
    for c in word:
        if stack and stack[-1] == c.swapcase():
            stack.pop()
        else:
            stack.append(c)
    return ''.join(stack)

def phi(word: str) -> str:
    images = {'a':'a'+'b'*100, 'A':'B'*100+'A', 'b':'b', 'B':'B'}
    return reduce_word(''.join(images[c] for c in word))

def suffix_array(s: str) -> list[int]:
    n = len(s)
    sa = list(range(n))
    ranks = [ord(c) for c in s]
    length = 1
    while True:
        sa.sort(key=lambda i: (ranks[i], ranks[i+length] if i+length<n else -1))
        nxt = [0]*n
        for j in range(1,n):
            a,b = sa[j-1],sa[j]
            ka = (ranks[a],ranks[a+length] if a+length<n else -1)
            kb = (ranks[b],ranks[b+length] if b+length<n else -1)
            nxt[b] = nxt[a] + (ka != kb)
        ranks = nxt
        if ranks[sa[-1]] == n-1:
            return sa
        length *= 2

def word_checks() -> dict:
    for i in range(-8, 31):
        check(phi(relator(i)) == relator(i+1), 'formal_endomorphism_identity')
    for i in range(1, 101):
        r = relator(i)
        check(len(r)==1300*i+104, 'relator_length')
        check(6*(200*i+27)<len(r), 'piece_bound_arithmetic')
        check(2*(100*i+15)<len(r), 'free_subgroup_half_bound')
        check(len(set(100*i+j for j in range(1,14)))==13, 'distinct_run_lengths')
        prefixes = [''.join('a'+'b'*(100*i+t) for t in range(1,j+1))
                    for j in range(1,13)]
        check(len(prefixes[-1])==1200*i+90, 'support_radius')
        check('a'+r[1:]==r, 'alternative_path_word')
    check(len(relator(0))==104, 'kernel_word_length')
    check(2*len(relator(0))<len(relator(1)), 'kernel_word_below_relator_half')

    # All rotations of the first five positive relators. Inverse rotations
    # have identical overlap statistics; mixed signs have no common letter.
    text_parts=[]
    starts: dict[int, tuple[int,int]]={}
    offset=0
    for i in range(1,6):
        r=relator(i)
        for j in range(len(r)):
            starts[offset+j]=(i,len(r))
        text_parts.append(r+r+chr(36+i))
        offset += 2*len(r)+1
    text=''.join(text_parts)
    ordered=[p for p in suffix_array(text) if p in starts]
    maxima={p:0 for p in ordered}
    comparisons=0
    for x,y in zip(ordered,ordered[1:]):
        lim=min(starts[x][1],starts[y][1])
        n=0
        while n<lim and text[x+n]==text[y+n]:
            n+=1
        maxima[x]=max(maxima[x],n)
        maxima[y]=max(maxima[y],n)
        comparisons+=1
    per_relator={}
    for p in ordered:
        i,length=starts[p]
        value=maxima[p]
        # Nearest lexical neighbours realize a suffix's maximal LCP with any
        # other selected suffix. Thus every selected rotation is covered.
        check(value<=200*i+27, 'finite_rotation_piece_maximum')
        check(6*value<length, 'finite_rotation_Cprime')
        per_relator[i]=max(per_relator.get(i,0),value)
    return {'positive_rotations':len(ordered), 'lexical_neighbor_comparisons':comparisons,
            'max_piece_by_relator':per_relator,
            'scope':'finite sample i=1,...,5; no infinite word-problem claim'}

def partitions(n: int):
    """Restricted-growth strings encoding every partition of {0,...,n-1}."""
    if n == 0:
        yield ()
        return
    def extend(prefix: tuple[int,...], high: int):
        if len(prefix)==n:
            yield prefix
        else:
            for j in range(high+2):
                yield from extend(prefix+(j,),max(high,j))
    yield from extend((0,),0)

def components(part: tuple[int,...], mask: int) -> tuple[int,...]:
    n=len(part)
    parent=list(range(n))
    def find(a: int) -> int:
        while parent[a]!=a:
            parent[a]=parent[parent[a]]
            a=parent[a]
        return a
    def union(a: int,b: int) -> None:
        a,b=find(a),find(b)
        parent[a]=b
    representatives={}
    for x,c in enumerate(part):
        if c in representatives:
            union(x,representatives[c])
        else:
            representatives[c]=x
    for x in range(n):
        if mask>>x & 1:
            union(x,(x+1)%n)
    return tuple(find(x) for x in range(n))

def priority_checks() -> dict:
    cases=0
    numbers={}
    # Arbitrary finite subrelations, all priority labellings with ties.
    for n,M in [(4,3),(5,3),(6,2)]:
        part_count=0
        for part in partitions(n):
            part_count+=1
            connectivity=[components(part,mask) for mask in range(1<<n)]
            candidates=[]
            for x in range(n):
                good=[]
                for mask in range(1<<n):
                    if mask>>x & 1:
                        continue
                    c=connectivity[mask]
                    if c[x]==c[(x+1)%n]:
                        good.append(mask)
                # Restrict to minimal support masks. This is an exact finite
                # model of valid paths using old connections and new edges.
                good.sort(key=int.bit_count)
                minimal=[]
                for mask in good:
                    if not any(old & mask == old for old in minimal):
                        minimal.append(mask)
                candidates.append(minimal)
            for rank in itertools.product(range(M),repeat=n):
                retained=0
                for x in range(n):
                    lower=sum(1<<y for y in range(n) if rank[y]<rank[x])
                    deletable=any(mask & lower == mask for mask in candidates[x])
                    if not deletable:
                        retained |= 1<<x
                c=components(part,retained)
                check(len(set(c))==1, 'simultaneous_priority_preserves_connectivity')
                cases+=1
        numbers[f'n={n},M={M}']=part_count
    return {'labelled_cases':cases,'partition_counts':numbers,
            'scope':'finite cycle permutations with every subequivalence relation; not quotients approximating the infinite group'}

def integral(profile: tuple[int,...]) -> Fraction:
    total=Fraction(0)
    for mask in range(1<<len(profile)):
        size=sum(profile[j] for j in range(len(profile)) if mask>>j & 1)
        total += Fraction((-1)**mask.bit_count(),1+size)
    return total

def probability_checks() -> dict:
    profiles=[(1,),(2,),(3,),(1,1),(1,2),(2,2),(1,1,1),(2,2,2)]
    perm_count=0
    tie_count=0
    for profile in profiles:
        n=1+sum(profile)
        blocks=[]
        cursor=1
        for size in profile:
            blocks.append(tuple(range(cursor,cursor+size)))
            cursor+=size
        retained=0
        for rank in itertools.permutations(range(n)):
            keep=not any(all(rank[v]<rank[0] for v in block) for block in blocks)
            retained+=keep
            perm_count+=1
        check(Fraction(retained,factorial(n))==integral(profile), 'exact_continuous_priority_integral')
        for M in [2,3]:
            kept=0
            for rank in itertools.product(range(M),repeat=n):
                kept+=not any(all(rank[v]<rank[0] for v in block) for block in blocks)
                tie_count+=1
            expected=Fraction(0)
            for r in range(M):
                p=Fraction(1)
                for size in profile:
                    p*=1-Fraction(r,M)**size
                expected+=p/M
            check(Fraction(kept,M**n)==expected, 'exact_tied_priority_formula')
    values=[]
    product=Fraction(1)
    for k in range(1,41):
        product*=Fraction(12*k,12*k+1)
        check(product**12<=Fraction(1,k), 'exact_integral_decay_bound')
        if k<=12:
            check(product==integral((12,)*k), 'exact_integral_product_formula')
        for M in [1,2,3,5,10,20]:
            rho=sum(((1-Fraction(r,M)**12)**k for r in range(M)),Fraction(0))/M
            check(product<=rho<=product+Fraction(1,M), 'exact_Riemann_error_bound')
        if k in [1,2,5,10,20,40]:
            values.append({'k':k,'I_decimal_display':float(product),
                           'I_exact':str(product)})
    # Exact route-length recurrence for finite-valued priorities.
    for k in range(1,20):
        B=1300*k+91
        distance=1
        for M in range(1,20):
            formula=12**(M-1)+B*(12**(M-1)-1)//11
            check(distance==formula,'route_length_recurrence')
            distance=B+12*distance
    return {'strict_priority_permutations':perm_count,
            'tied_priority_labelings':tie_count,
            'sample_integrals':values}

def compose(p: tuple[int,...],q: tuple[int,...]) -> tuple[int,...]:
    return tuple(p[q[i]] for i in range(len(p)))

def pow_perm(p: tuple[int,...],e: int) -> tuple[int,...]:
    if e<0:
        inv=[0]*len(p)
        for i,j in enumerate(p): inv[j]=i
        return pow_perm(tuple(inv),-e)
    r=tuple(range(len(p)))
    while e:
        if e&1: r=compose(r,p)
        p=compose(p,p);e//=2
    return r

def finite_quotient_checks() -> dict:
    count=0
    hom_patterns=0
    for n in [3,4]:
        perms=list(itertools.permutations(range(n)))
        ident=tuple(range(n))
        for a,b in itertools.product(perms,repeat=2):
            d=1
            while pow_perm(b,d)!=ident: d+=1
            def evaluate(i: int):
                result=ident
                for j in range(1,14):
                    result=compose(result,compose(a,pow_perm(b,100*i+j)))
                return result
            check(evaluate(d)==evaluate(0),'finite_quotient_periodicity')
            if all(evaluate(i)==ident for i in range(1,d+1)):
                check(evaluate(0)==ident,'finite_model_kernel_word_vanishes')
                hom_patterns+=1
            count+=1
    return {'pairs_tested':count,'pairs_satisfying_full_period':hom_patterns,
            'scope':'finite periodicity identity only; nontriviality of the word in G is a written Greendlinger deduction'}

def main() -> None:
    parser=argparse.ArgumentParser()
    parser.add_argument('--output',type=Path,default=Path('checks.json'))
    args=parser.parse_args()
    start=time.perf_counter()
    results={'word_checks':word_checks(),'priority_checks':priority_checks(),
             'probability_checks':probability_checks(),
             'finite_quotient_checks':finite_quotient_checks()}
    result={'status':'PASS','scope':'exact finite checks, not a formal or independent verification of infinite theorems',
            'assertions':dict(COUNTS),'total_exact_assertions':sum(COUNTS.values()),
            'results':results,'elapsed_seconds':round(time.perf_counter()-start,3)}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':result['status'],'total_exact_assertions':result['total_exact_assertions'],
                      'elapsed_seconds':result['elapsed_seconds'],'output':str(args.output)},indent=2))

if __name__=='__main__':
    main()
