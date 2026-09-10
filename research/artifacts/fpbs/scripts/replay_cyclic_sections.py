#!/usr/bin/env python3
"""Exact finite checks of common-cyclic-section graphing normalization.

Not a test of infinite cost theorems, Suchkova-Shunkov, or either conjecture.
Python 3.10+, standard library only. Reuses the included finite group tables.
"""
from __future__ import annotations
import argparse,json,itertools
from fractions import Fraction
from pathlib import Path
from replay_bounded_exponent import cyclic,abelian,symmetric,dihedral,quaternion,Group

def orbits(G:Group,K:frozenset[int])->list[set[int]]:
    unseen=set(range(G.n));result=[]
    while unseen:
        a=min(unseen);part={G.mul(a,k) for k in K}
        result.append(part);unseen-=part
    return result

def star(points:set[int])->set[tuple[int,int]]:
    if not points:return set()
    a=min(points)
    return {(min(a,b),max(a,b)) for b in points if b!=a}

def connected(n:int,edges:set[tuple[int,int]])->bool:
    adj=[set() for _ in range(n)]
    for a,b in edges:adj[a].add(b);adj[b].add(a)
    seen={0};todo=[0]
    while todo:
        a=todo.pop()
        for b in adj[a]-seen:seen.add(b);todo.append(b)
    return len(seen)==n

def main()->None:
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,default=Path(__file__).resolve().parents[1]/'research/artifacts/cyclic-section-checks.json');args=p.parse_args()
    groups=[cyclic(3),cyclic(6),abelian((2,2,2)),dihedral(4),quaternion(),symmetric(3),symmetric(4,True),symmetric(4)]
    assertions=0;cases=0;rows=[]
    def check(v:bool)->None:
        nonlocal assertions
        if not v:raise AssertionError('cyclic section identity or graph connectivity')
        assertions+=1
    for G in groups:
        starts=cases
        for d in range(1,4):
            gens=[]
            for S in itertools.combinations([x for x in range(G.n) if x!=G.identity],d):
                if len(G.closure(S))==G.n:
                    gens.append(S)
                    if len(gens)==4:break
            for S in gens:
                for g in range(G.n):
                    H=G.closure([g]);ell=len(H);parts=orbits(G,H)
                    A={min(c) for c in parts}
                    graph=set().union(*(star(c) for c in parts))
                    total=len(graph)
                    check(Fraction(total,G.n)==1-Fraction(1,ell))
                    rhs=Fraction(1)+Fraction(d-1,ell)
                    for s in S:
                        Hi=G.closure([s,g]);k=len(Hi)
                        pieces=[c&A for c in orbits(G,Hi)]
                        section_edges=set().union(*(star(c) for c in pieces))
                        expected=Fraction(1,ell)-Fraction(1,k)
                        check(Fraction(len(section_edges),G.n)==expected)
                        check(all(len(c)==k//ell for c in pieces))
                        graph|=section_edges;total+=len(section_edges);rhs-=Fraction(1,k)
                    check(Fraction(total,G.n)==rhs)
                    check(connected(G.n,graph))
                    check(Fraction(len(graph),G.n)>=1-Fraction(1,G.n))
                    cases+=1
        rows.append({'group':G.name,'order':G.n,'cases':cases-starts})
    result={'status':'PASS','finite_graphing_cases':cases,'exact_assertions':assertions,'groups':rows,
            'scope':'Exact finite cyclic-section graphing normalization and connectivity only. Not proof verification of infinite-action or algebraic theorems.'}
    args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
