#!/usr/bin/env python3
"""Finite verification and outward-rounded evaluation of a graphing bound.

These tests are not a proof of any infinite-group theorem. Numeric minima are
not used: certified evaluations use explicitly specified rational parameters.
"""
from __future__ import annotations
import argparse
from collections import Counter
from decimal import Decimal, localcontext, ROUND_FLOOR, ROUND_CEILING
from fractions import Fraction
from itertools import permutations
import json
from pathlib import Path

PREC=80

def calc(rounding, fn):
    with localcontext() as ctx:
        ctx.prec=PREC; ctx.rounding=rounding
        return +fn()

def rat(a:int,b:int=1):
    return (calc(ROUND_FLOOR,lambda:Decimal(a)/Decimal(b)),
            calc(ROUND_CEILING,lambda:Decimal(a)/Decimal(b)))

def add(x,y):
    return(calc(ROUND_FLOOR,lambda:x[0]+y[0]),calc(ROUND_CEILING,lambda:x[1]+y[1]))

def sub(x,y):
    return(calc(ROUND_FLOOR,lambda:x[0]-y[1]),calc(ROUND_CEILING,lambda:x[1]-y[0]))

def mul(x,y):
    lows=[calc(ROUND_FLOOR,lambda:a*b) for a in x for b in y]
    highs=[calc(ROUND_CEILING,lambda:a*b) for a in x for b in y]
    return min(lows),max(highs)

def powi(x,k:int):
    if k<0: raise ValueError('integer exponent must be nonnegative')
    out=rat(1)
    while k:
        if k&1: out=mul(out,x)
        k//=2
        if k: x=mul(x,x)
    return out

def certified_bound(n:int,pnum:int,pden:int):
    if n<3 or not 0<pnum<pden: raise ValueError('invalid bound parameters')
    one=rat(1);p=rat(pnum,pden)
    D=powi(sub(one,powi(p,n-1)),n)
    U=sub(add(add(sub(one,rat(1,n)),p),mul(sub(one,p),D)),mul(powi(p,n),rat(1,n)))
    return {'n':n,'q_numerator':pnum,'q_denominator':pden,
            'lower':str(U[0]),'upper':str(U[1]),
            'baseline_lower':str(sub(rat(2),rat(2,n))[0]),
            'strict_improvement_certified':U[1]<sub(rat(2),rat(2,n))[0]}

def compose(g,h): return tuple(g[h[i]] for i in range(len(g)))
def sign(g): return (-1)**sum(g[i]>g[j] for i in range(len(g)) for j in range(i+1,len(g)))
def order(g):
    e=tuple(range(len(g)));u=e;k=0
    while True:
        k+=1;u=compose(u,g)
        if u==e:return k

def powers(g):
    u=tuple(range(len(g))); out=[]
    for _ in range(order(g)):
        out.append(u);u=compose(u,g)
    return out

def generated(gens):
    e=tuple(range(len(gens[0]))); seen={e};todo=[e]
    while todo:
        g=todo.pop()
        for h in gens:
            u=compose(g,h)
            if u not in seen:seen.add(u);todo.append(u)
    return seen

class DSU:
    def __init__(self,n):self.p=list(range(n))
    def find(self,x):
        while self.p[x]!=x:
            self.p[x]=self.p[self.p[x]];x=self.p[x]
        return x
    def join(self,x,y):
        x=self.find(x);y=self.find(y)
        if x!=y:self.p[y]=x


def finite_case(name,group,a,b):
    group=sorted(group);ix={g:i for i,g in enumerate(group)};v=len(group)
    h=order(b);m=order(a);H=powers(b)
    assert generated([a,b])==set(group)
    cs=[compose(a,t) for t in H]
    Ps=[powers(c)[1:] for c in cs]
    flat=[g for P in Ps for g in P]
    assert len(set(flat))==len(flat),'disjoint support hypothesis failed'
    support_masks=[]
    for x in group:
        support_masks.append([sum(1<<ix[compose(x,g)] for g in P) for P in Ps])
    aper=[ix[compose(x,a)] for x in group]
    acycles=[];bcycles=[]
    for generator,target in [(a,acycles),(b,bcycles)]:
        seen=set()
        for i,x in enumerate(group):
            if i in seen:continue
            C=[ix[compose(x,g)] for g in powers(generator)]
            seen.update(C);target.append(C)
    bins=Counter();checks=0
    for mask in range(1<<v):
        A=mask
        for x in range(v):
            if not any(mask&P==P for P in support_masks[x]):A|=1<<x
        fullA=0;fullU=0;pruned=A
        for C in acycles:
            cm=sum(1<<z for z in C)
            if A&cm==cm:
                fullA+=len(C);pruned &= ~(1<<min(C))
            if mask&cm==cm:fullU+=len(C)
        assert pruned.bit_count()==A.bit_count()-fullA//m;checks+=1
        d=DSU(v)
        for C in bcycles:
            root=min(C)
            for x in C:
                if x!=root:d.join(root,x)
        for x in range(v):
            if pruned>>x&1:d.join(x,aper[x])
        assert len({d.find(x) for x in range(v)})==1;checks+=1
        assert fullA>=fullU;checks+=1
        k=mask.bit_count()
        bins[(k,'A')]+=A.bit_count()
        bins[(k,'Ufull')]+=fullU
        bins[(k,'actual_pruned')]+=pruned.bit_count()
    budgets=[]
    for q in [Fraction(1,4),Fraction(1,2),Fraction(3,4)]:
        EA=sum(Fraction(val,v)*q**k*(1-q)**(v-k) for (k,kind),val in bins.items() if kind=='A')
        EUfull=sum(Fraction(val,v)*q**k*(1-q)**(v-k) for (k,kind),val in bins.items() if kind=='Ufull')
        actual=sum(Fraction(val,v)*q**k*(1-q)**(v-k) for (k,kind),val in bins.items() if kind=='actual_pruned')
        prod=Fraction(1)
        for P in Ps:prod*=1-q**len(P)
        predicted=q+(1-q)*prod
        assert EA==predicted;checks+=1
        assert EUfull==q**m;checks+=1
        assert actual<=predicted-q**m/m;checks+=1
        budgets.append({'q':str(q),'unpruned_expectation':str(EA),
                        'pruned_expectation':str(actual),
                        'proved_pruned_upper_bound':str(predicted-q**m/m)})
    return {'group':name,'order':v,'subgroup_order':h,'a_order':m,
            'cycle_orders':[order(c) for c in cs], 'all_labelings':1<<v,
            'exact_assertions':checks,'expectations':budgets}

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--output',default='checks.json');args=parser.parse_args()
    S3=list(permutations(range(3)))
    a3=(1,0,2);b3=(1,2,0)
    A4=[g for g in permutations(range(4)) if sign(g)==1]
    b4=(1,2,0,3)
    pair=None
    for a4 in A4:
        if order(a4)!=3 or generated([a4,b4])!=set(A4):continue
        Ps=[powers(compose(a4,h))[1:] for h in powers(b4)]
        f=[x for P in Ps for x in P]
        if len(f)==len(set(f)):
            pair=a4;break
    assert pair is not None
    cases=[finite_case('S_3',S3,a3,b3),finite_case('A_4',A4,pair,b4)]
    vals=[certified_bound(n,num,10**12) for n,num in
          [(1003,994178849016),(10001,999199197055),
           (100003,999897808420),(1000003,999987546714)]]
    # Cross-check interval arithmetic against exact small rational formulas.
    interval_checks=0
    for n in range(3,16):
        for den in [4,7,10]:
            for num in range(1,den):
                q=Fraction(num,den)
                val=1-Fraction(1,n)+q+(1-q)*(1-q**(n-1))**n-q**n/n
                cert=certified_bound(n,num,den)
                assert Fraction(Decimal(cert['lower']))<=val<=Fraction(Decimal(cert['upper']))
                interval_checks+=1
    out={'status':'finite checks passed','not_a_formal_infinite_proof':True,
         'finite_models':cases,'labelings_total':sum(x['all_labelings'] for x in cases),
         'exact_assertions':sum(x['exact_assertions'] for x in cases)+interval_checks,
         'interval_enclosure_crosschecks':interval_checks,
         'certified_rational_parameter_evaluations':vals,
         'minimizer_certification':'None. Each row is an upper bound evaluated at a specified rational q, not a certified global minimum.',
         'not_verified':['Burnside centralizers and embeddings','measurable partitions in infinite actions',
                         'action-cost infima','Fixed Price','Benjamini-Schramm']}
    Path(args.output).write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))
if __name__=='__main__':main()
