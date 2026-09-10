#!/usr/bin/env python3
"""Finite checks for bounded-exponent cost arguments, not a theorem prover.

Python 3.10+, standard library only. All group/counting tests are exact.
The separate parameter table uses floating-point arithmetic.
"""
from __future__ import annotations
import argparse
import itertools
import json
import math
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Callable, Iterable

COUNTS: Counter[str] = Counter()

def check(condition: bool, category: str) -> None:
    if not condition:
        raise AssertionError(category)
    COUNTS[category] += 1

@dataclass
class Group:
    name: str
    table: list[list[int]]
    identity: int

    def __post_init__(self) -> None:
        self.n = len(self.table)
        self.inv = [next(j for j in range(self.n) if self.table[i][j] == self.identity
                         and self.table[j][i] == self.identity) for i in range(self.n)]
        self.orders = [self.order(i) for i in range(self.n)]
        self.exponent = math.lcm(*self.orders)

    def mul(self, a: int, b: int) -> int:
        return self.table[a][b]

    def power(self, a: int, k: int) -> int:
        if k < 0:
            return self.power(self.inv[a], -k)
        r = self.identity
        for _ in range(k):
            r = self.mul(r, a)
        return r

    def order(self, a: int) -> int:
        r = self.identity
        for k in range(1, self.n + 1):
            r = self.mul(r, a)
            if r == self.identity:
                return k
        raise ValueError("not a finite group")

    def closure(self, gens: Iterable[int]) -> frozenset[int]:
        steps = set(gens)
        steps |= {self.inv[g] for g in list(steps)}
        seen = {self.identity}
        todo = [self.identity]
        while todo:
            x = todo.pop()
            for s in steps:
                y = self.mul(x, s)
                if y not in seen:
                    seen.add(y)
                    todo.append(y)
        return frozenset(seen)

    def subgroups(self) -> list[frozenset[int]]:
        trivial = frozenset([self.identity])
        seen = {trivial}
        todo = [trivial]
        while todo:
            K = todo.pop()
            for a in range(self.n):
                if a in K:
                    continue
                L = self.closure(set(K) | {a})
                if L not in seen:
                    seen.add(L)
                    todo.append(L)
        return sorted(seen, key=lambda K: (len(K), tuple(sorted(K))))

    def centralizer(self, w: int) -> set[int]:
        return {x for x in range(self.n) if self.mul(x, w) == self.mul(w, x)}


def from_elements(name: str, elems: list, op: Callable, identity) -> Group:
    index = {x: i for i, x in enumerate(elems)}
    return Group(name, [[index[op(x, y)] for y in elems] for x in elems], index[identity])


def cyclic(n: int) -> Group:
    return from_elements(f'C{n}', list(range(n)), lambda a,b:(a+b)%n, 0)


def abelian(moduli: tuple[int, ...]) -> Group:
    elems = list(itertools.product(*[range(m) for m in moduli]))
    return from_elements('x'.join(f'C{m}' for m in moduli), elems,
                         lambda a,b: tuple((a[i]+b[i])%m for i,m in enumerate(moduli)),
                         tuple(0 for _ in moduli))


def symmetric(n: int, alternating: bool=False) -> Group:
    def parity(p):
        return sum(p[i]>p[j] for i in range(n) for j in range(i+1,n))%2
    elems=[p for p in itertools.permutations(range(n)) if not alternating or parity(p)==0]
    return from_elements(('A' if alternating else 'S')+str(n),elems,
                         lambda p,q:tuple(p[q[i]] for i in range(n)),tuple(range(n)))


def dihedral(m: int) -> Group:
    return from_elements(f'D{2*m}',list(itertools.product(range(m),range(2))),
                         lambda a,b:((a[0]+(-1)**a[1]*b[0])%m,(a[1]+b[1])%2),(0,0))


def quaternion() -> Group:
    basis = [[(0,0),(0,1),(0,2),(0,3)],
             [(0,1),(1,0),(0,3),(1,2)],
             [(0,2),(1,3),(1,0),(0,1)],
             [(0,3),(0,2),(1,1),(1,0)]]
    def mul(a,b):
        s,k=basis[a[1]][b[1]]
        return ((a[0]+b[0]+s)%2,k)
    return from_elements('Q8',list(itertools.product(range(2),range(4))),mul,(0,0))


def first_returns(G: Group, K: frozenset[int], a: int):
    result={}
    for c in sorted({G.mul(a,b) for b in K}):
        d=next(j for j in range(1,G.orders[c]+1) if G.power(c,j) in K)
        P=frozenset(G.power(c,j) for j in range(1,d))
        result[c]=(d,P)
    return result


def packing(data):
    chosen=[]
    used=set()
    for c,(d,P) in data.items():
        if used.isdisjoint(P):
            chosen.append((c,d,P))
            used.update(P)
    return chosen,used


class DSU:
    def __init__(self,n): self.p=list(range(n))
    def find(self,x):
        while self.p[x]!=x:
            self.p[x]=self.p[self.p[x]]
            x=self.p[x]
        return x
    def join(self,a,b):
        a,b=self.find(a),self.find(b)
        if a!=b: self.p[b]=a


def algebra_checks(G: Group) -> dict:
    check(all(G.mul(G.mul(a,b),c)==G.mul(a,G.mul(b,c))
              for a in range(G.n) for b in range(G.n) for c in range(G.n)),
          'group_associativity')
    subs=G.subgroups()
    for K in subs:
        for a in set(range(G.n))-K:
            data=first_returns(G,K,a)
            coset=set(data)
            for c,(d,P) in data.items():
                check(2<=d<=G.exponent and len(P)==d-1 and P.isdisjoint(K)
                      and G.power(c,d) in K,'first_return_properties')
                b=G.mul(G.inv[a],c)
                current=G.mul(a,b)
                for j in range(1,d):
                    check(current==G.power(c,j),'detour_selected_start')
                    current=G.mul(G.mul(current,a),b)
                current=G.mul(current,G.inv[G.power(c,d)])
                check(b in K and current==G.identity,'first_return_word_closes')
            for w in set(range(G.n))-K:
                C=G.centralizer(w)
                inter=coset&C
                if inter:
                    c0=min(inter)
                    check(inter=={G.mul(c0,l) for l in K&C},'centralizer_coset_identity')
                check({c for c,(_,P) in data.items() if w in P}<=inter,'power_fiber_in_centralizer')
            chosen,W=packing(data)
            check(all(P&W for _,P in data.values()),'maximal_packing_hitting_set')
            sizes={w:len(set(K)&G.centralizer(w)) for w in W}
            check(len(K)<=sum(sizes.values()),'hitting_set_centralizer_count')
            check(max(sizes.values())*len(W)>=len(K),'large_centralizer_witness')
            check(len(W)<=len(chosen)*(G.exponent-1),'bounded_witness_union')
        # Exact finite centralizer transversal, for every external element.
        for w in set(range(G.n))-K:
            L=set(K)&G.centralizer(w)
            remaining=set(range(G.n)); A=set()
            while remaining:
                x=min(remaining); A.add(x)
                remaining-={G.mul(x,l) for l in L}
            check(Fraction(len(A),G.n)==Fraction(1,len(L)), 'transversal_cost')
            graph=DSU(G.n)
            for x in range(G.n):
                for k in K: graph.join(x,G.mul(x,k))
            for x in A: graph.join(x,G.mul(x,w))
            check(all(graph.find(x)==graph.find(G.mul(x,w)) for x in range(G.n)),
                  'commuting_transversal_generates_edges')
    return {'group':G.name,'order':G.n,'exponent':G.exponent,'subgroups':len(subs)}


def coloring_checks(G: Group,K: frozenset[int],a:int) -> dict:
    data=first_returns(G,K,a)
    chosen,_=packing(data)
    J=G.closure(set(K)|{a})
    pnum,pden=1,3
    weighted_A=0;weighted_D=0
    for mask in range(1<<G.n):
        A={x for x in range(G.n) if (mask>>x)&1}
        D={x for x in range(G.n) if not any(
            all(G.mul(x,g) in A for g in P) for _,_,P in chosen)}
        graph=DSU(G.n)
        for x in range(G.n):
            for k in K: graph.join(x,G.mul(x,k))
        for x in A|D: graph.join(x,G.mul(x,a))
        check(all(graph.find(x)==graph.find(G.mul(x,a)) for x in range(G.n)),
              'all_labelings_paid_repair')
        check(all((graph.find(x)==graph.find(y))==(G.mul(G.inv[x],y) in J)
                  for x in range(G.n) for y in range(G.n)),
              'all_labelings_exact_generated_relation')
        weight=pnum**len(A)*(pden-pnum)**(G.n-len(A))
        weighted_A+=len(A)*weight;weighted_D+=len(D)*weight
    q=Fraction(pnum,pden)
    failure=math.prod(1-q**len(P) for _,_,P in chosen)
    check(Fraction(weighted_A,G.n*pden**G.n)==q,'exact_selector_mean')
    check(Fraction(weighted_D,G.n*pden**G.n)==failure,'exact_product_failure_mean')
    check(failure <= (1-q**(G.exponent-1))**len(chosen),'exact_uniform_failure_bound')
    return {'group':G.name,'subgroup_order':len(K),'element':a,
            'witness_sizes':[len(P) for _,_,P in chosen],
            'colorings':1<<G.n,'failure_probability_q_one_third':str(failure)}


def shared_root_checks() -> list[dict]:
    Q=quaternion();out=[]
    # In this encoding i=1 and -1=4.
    for r in range(7):
        h=2**r
        def mul(x,y): return (Q.mul(x[0],y[0]),x[1]^y[1])
        def power(c,j):
            x=(0,0)
            for _ in range(j):x=mul(x,c)
            return x
        H={(0,v) for v in range(h)}
        K=H|{(4,v) for v in range(h)}
        a=(1,0);w=(4,0)
        coset={mul(a,b) for b in H}
        full=[{power(c,j) for j in (1,2,3)} for c in coset]
        check(all(w in P for P in full),'quaternion_shared_external_root')
        check(all(mul(l,w)==mul(w,l) for l in H),'quaternion_root_centralizes_subgroup')
        enlarged={mul(a,b) for b in K}
        check(all(power(c,2) in K and c not in K for c in enlarged),
              'quaternion_absorption_first_return_two')
        check(len(enlarged)==2*h,'quaternion_after_absorption_disjoint_singletons')
        out.append({'elementary_rank':r,'initial_subgroup_order':h,
                    'shared_root':[-1,0], 'disjoint_detours_after_absorption':2*h})
    return out


def parameter_checks() -> list[dict]:
    out=[]
    for N in (2,3,4,8,16):
        for h in (3,8,32,256,1000,1000000):
            q=((N-1)*math.log(h)/h)**(1/N)
            if q>=1: continue
            k=math.ceil(h*q/(N-1))
            x=q**(N-1)
            log_failure=k*math.log1p(-x)
            # These are explicitly numerical sanity checks, not exact assertions.
            if not (log_failure <= -math.log(h)+1e-10 and
                    (k-1)*(N-1)/h < q+1e-14):
                raise AssertionError('numerical_parameter_bound')
            out.append({'N':N,'h':h,'q':q,'k':k,
                        'log_failure_bound':log_failure,
                        'log_one_over_h':-math.log(h)})
    return out


def main() -> None:
    parser=argparse.ArgumentParser()
    parser.add_argument('--output',type=Path,default=Path(__file__).resolve().parents[1]/
                        'research/artifacts/bounded-exponent-checks.json')
    args=parser.parse_args()
    groups=[cyclic(3),cyclic(4),cyclic(6),cyclic(8),abelian((2,2,2)),
            abelian((4,2)),symmetric(3),dihedral(4),quaternion(),symmetric(4,True),symmetric(4)]
    algebra=[algebra_checks(G) for G in groups]
    lookup={G.name:G for G in groups}
    models=[]
    for name,korder in [('C8',2),('C8',4),('C2xC2xC2',4),('C4xC2',2),
                        ('S3',2),('D8',2),('Q8',1),('Q8',2),('A4',3)]:
        G=lookup[name]
        K=next(K for K in G.subgroups() if len(K)==korder)
        a=next(a for a in range(G.n) if a not in K)
        models.append(coloring_checks(G,K,a))
    collisions=shared_root_checks()
    numerical=parameter_checks()
    result={'status':'PASS','exact_assertions':sum(COUNTS.values()),
            'exact_assertions_by_category':dict(sorted(COUNTS.items())),
            'finite_groups':algebra,'exhaustive_coloring_models':models,
            'total_exhaustive_colorings':sum(x['colorings'] for x in models),
            'shared_root_models':collisions,'numerical_parameter_checks':numerical,
            'scope':'Exact finite algebra/counting and separate numerical parameter checks only. '
                    'Not a formal verification of infinite-action cost theorems, '
                    'Held or Burnside inputs, novelty, or either universal conjecture.'}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ('status','exact_assertions','total_exhaustive_colorings')},indent=2))

if __name__=='__main__':main()
