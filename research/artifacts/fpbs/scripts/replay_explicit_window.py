#!/usr/bin/env python3
"""Finite audits of the explicit-window proof; not an infinite theorem prover."""
from __future__ import annotations
import argparse
from collections import Counter, defaultdict
from decimal import Decimal, localcontext
from fractions import Fraction as Q
from itertools import product
import json
from pathlib import Path
import random


def reduce_word(word: str) -> str:
    out: list[str] = []
    for ch in word:
        if out and ch == out[-1].swapcase():
            out.pop()
        else:
            out.append(ch)
    return ''.join(out)


def inverse(word: str) -> str:
    return word.swapcase()[::-1]


def run_length(word: str) -> int:
    best = cur = 0
    prev = None
    for c in word:
        sign = c.islower()
        cur = cur + 1 if sign == prev else 1
        best = max(best, cur)
        prev = sign
    return best


def reduced_words(max_len: int):
    level = ['']
    for _ in range(max_len):
        nxt = []
        for w in level:
            for c in 'abAB':
                if w and c == w[-1].swapcase():
                    continue
                v = w + c
                nxt.append(v)
                yield v
        level = nxt


def substitute(word: str, a: str, b: str) -> str:
    table = {'a': a, 'b': b, 'A': inverse(a), 'B': inverse(b)}
    return ''.join(table[c] for c in word)


def poly_add(a, b):
    z = [Q(0)] * max(len(a), len(b))
    for i, c in enumerate(a): z[i] += c
    for i, c in enumerate(b): z[i] += c
    return z


def poly_mul(a, b):
    z = [Q(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b): z[i+j] += x*y
    return z


def matmul(a, b):
    n = len(a)
    return [[sum(a[i][k]*b[k][j] for k in range(n)) for j in range(n)] for i in range(n)]


def matrix_from_graph(adj):
    return [[int(j in adj[i]) for j in range(len(adj))] for i in range(len(adj))]


def direct_nonbacktracking(adj, max_len):
    n = len(adj)
    result = [[[0]*n for _ in range(n)] for _ in range(max_len+1)]
    for start in range(n):
        states = {(None, start): 1}
        result[0][start][start] = 1
        for step in range(1, max_len+1):
            nxt = defaultdict(int)
            for (prev, cur), count in states.items():
                for nb in adj[cur]:
                    if nb != prev: nxt[(cur, nb)] += count
            for (_, cur), count in nxt.items(): result[step][start][cur] += count
            states = nxt
    return result


def main(output: Path):
    counts = Counter()
    def check(test, name):
        counts[name] += 1
        if not test:
            raise AssertionError(f'failed {name}, assertion {counts[name]}')

    # Endpoint and exact offspring-law calculations.
    p = Q(7,20)
    f = [1-p,p]
    m, B = p, Q(0)
    for j in range(6):
        check(sum(f)==1, 'offspring_pgf')
        check(all(c>=0 for c in f), 'offspring_pgf')
        check(sum(k*c for k,c in enumerate(f))==m, 'offspring_pgf')
        check(sum(k*(k-1)*c for k,c in enumerate(f))==B, 'offspring_pgf')
        if j<5:
            h = poly_add([1-p], [p*c for c in f])
            f = poly_mul([1-p,p], poly_mul(h,h))
            m, B = p+2*p*m, 4*p*p*m+2*p*p*m*m+2*p*B
    check(m==Q(2058819,2000000), 'rational_endpoint')
    check(m>1, 'rational_endpoint')
    check(len(f)==64, 'offspring_pgf')
    z = p*2*(m-1)/B
    root_lower = 1-(1-z)**4
    check(z==Q(23527600000,1803394208413), 'rational_endpoint')
    check(root_lower>Q(1,20), 'rational_endpoint')
    check(Q(26,15)**2>3, 'radical_upper_bounds')
    check(Q(107,5)**2>455, 'radical_upper_bounds')
    check(4*(1+Q(26,15)+Q(107,5)/24)==Q(29,2), 'radical_upper_bounds')
    check(Q(29,2)<Q(381,100)**2, 'radical_upper_bounds')
    up = Q(37,100)
    den = 1-Q(381,100)*up+3*up*up
    check(den==Q(1,1000), 'rational_endpoint')
    check(3*up*up<1, 'rational_endpoint')
    check(Q(1000)*Q(381,400)**300<Q(1,800), 'rational_endpoint')
    lo, hi = Q(0), Q(1)
    def mean(t): return sum(Q(2)**j*t**(j+1) for j in range(6))
    for _ in range(96):
        mid = (lo+hi)/2
        if mean(mid)<1: lo=mid
        else: hi=mid
    check(mean(lo)<1<=mean(hi), 'critical_root_bracket')
    check(hi< p, 'critical_root_bracket')

    # The sixteen-term identity is a formal identity in the free group ring.
    lhs = defaultdict(Q)
    for u,v in product('abAB',repeat=2): lhs[reduce_word(u+v)] += Q(1,16)
    rhs = defaultdict(Q)
    rhs[''] += Q(1,4)
    for pair in [('aa','bb'),('aB','Ab'),('ab','ba')]:
        for w in [pair[0], inverse(pair[0]), pair[1], inverse(pair[1])]:
            rhs[reduce_word(w)] += Q(1,16)
    check(dict(lhs)==dict(rhs), 'formal_spectral_identity')

    # Finite word tests do NOT decide injectivity in the infinite presented group.
    patterns = set()
    for i in range(1,7):
        base = 'a'+'b'*i
        length = (13*len(base))//2+1
        for shift in range(len(base)):
            pat = (base*20)[shift:shift+length]
            patterns.add(pat)
            patterns.add(inverse(pat))
    words_sq = words_cross = 0
    for w in reduced_words(8):
        x = substitute(w,'aa','bb')
        check(reduce_word(x)==x, 'square_subgroup_words')
        check(not any(pat in x for pat in patterns), 'square_subgroup_words')
        words_sq += 1
        x = substitute(w,'aB','Ab')
        check(reduce_word(x)==x, 'cross_subgroup_words')
        check(run_length(x)<=2, 'cross_subgroup_words')
        words_cross += 1
    free_product_words = 0
    exponents = tuple(range(-6,0))+tuple(range(1,7))
    for syllables in range(1,5):
        for first in range(2):
            for exps in product(exponents,repeat=syllables):
                parts=[]
                for j,k in enumerate(exps):
                    base=('ab','ba')[(first+j)%2]
                    parts.append((base if k>0 else inverse(base))*abs(k))
                x=''.join(parts)
                check(reduce_word(x)==x, 'cyclic_free_product_words')
                check(not any(pat in x for pat in patterns), 'cyclic_free_product_words')
                free_product_words += 1

    # Reproducible stress tests of the linear junction bound (sampled, not exhaustive).
    rng=random.Random(20260909)
    def allowed_word(n):
        out=''
        for _ in range(n):
            possible=[c for c in 'abAB' if (not out or c!=out[-1].swapcase()) and run_length(out+c)<=6]
            out += rng.choice(possible)
        return out
    for _ in range(5000):
        v=allowed_word(rng.randrange(1,101));w=allowed_word(rng.randrange(1,101))
        check(run_length(reduce_word(inverse(v)+w))<=12, 'sampled_linear_junctions')

    # Direct walk counts versus the adjacency-polynomial recurrence.
    graphs={}
    graphs['K5']=[set(range(5))-{i} for i in range(5)]
    graphs['octahedral']=[{j for j in range(6) if j//2!=i//2} for i in range(6)]
    for side in (3,4):
        adj=[]
        for x in range(side):
            for y in range(side):
                adj.append({((x+dx)%side)*side+(y+dy)%side for dx,dy in [(1,0),(-1,0),(0,1),(0,-1)]})
        graphs[f'torus_{side}x{side}']=adj
    nb_summary={}
    for name,adj in graphs.items():
        n=len(adj);check(all(len(s)==4 for s in adj),'finite_graph_degree')
        ns=direct_nonbacktracking(adj,12);A=matrix_from_graph(adj)
        eye=[[int(i==j) for j in range(n)] for i in range(n)]
        check(ns[0]==eye and ns[1]==A,'nonbacktracking_matrices')
        aa=matmul(A,A)
        check(ns[2]==[[aa[i][j]-4*eye[i][j] for j in range(n)] for i in range(n)],'nonbacktracking_matrices')
        for k in range(3,13):
            prodA=matmul(A,ns[k-1])
            check(ns[k]==[[prodA[i][j]-3*ns[k-2][i][j] for j in range(n)] for i in range(n)],'nonbacktracking_matrices')
        nb_summary[name]={'vertices':n,'lengths_checked':'0 through 12'}

    # Finite cactus subsets test the edge-boundary ledger, not an infinite spectral norm.
    def cactus(order,cycles):
        edges=set();deg=Counter();n=1
        for _ in range(cycles):
            available=[v for v in range(n) if deg[v]<=2]
            root=rng.choice(available)
            cycle=[root]+list(range(n,n+order-1));n+=order-1
            for j in range(order):
                u,v=cycle[j],cycle[(j+1)%order]
                edges.add(tuple(sorted((u,v))));deg[u]+=1;deg[v]+=1
        return n,edges
    cactus_subsets=0
    for order in (3,5,7,13,17):
        for cycles in (1,2,3,4):
            n,edges=cactus(order,cycles)
            for _ in range(100):
                subset={v for v in range(n) if rng.randrange(2)}
                if not subset: continue
                inside=sum(u in subset and v in subset for u,v in edges)
                boundary=4*len(subset)-2*inside
                check(Q(boundary)>=Q(2*(order-2),order-1)*len(subset),'sampled_cactus_boundaries')
                cactus_subsets+=1

    with localcontext() as ctx:
        ctx.prec=70
        sqrt3=Decimal(3).sqrt();sqrt455=Decimal(455).sqrt()
        Dstar=2*(1+sqrt3+sqrt455/24).sqrt()
        threshold=(Dstar-(Dstar*Dstar-12).sqrt())/6
        safe=(Decimal(29).sqrt()-Decimal(5).sqrt())/(6*Decimal(2).sqrt())
        numeric={
          'alpha6_lower':str(Decimal(lo.numerator)/Decimal(lo.denominator)),
          'alpha6_upper':str(Decimal(hi.numerator)/Decimal(hi.denominator)),
          'D_star':str(Dstar),
          'p_u_lower_sharp_spectral_expression':str(threshold),
          'p_u_lower_safe_radical':str(safe),
          'theta_lower_at_7_over_20':str(Decimal(root_lower.numerator)/Decimal(root_lower.denominator)),
        }
    result={
      'status':'PASS',
      'date':'2026-09-09',
      'scope':'finite combinatorial and rational checks only; not formal or infinite-theorem verification',
      'exact_assertions_total':sum(counts.values()),
      'assertion_counts':dict(counts),
      'rational_endpoints':{'lower':'7/20','upper':'37/100','offspring_mean':str(m),'one_root_branch_survival_lower':str(z),'root_survival_lower':str(root_lower),'operator_denominator_at_upper':str(den)},
      'exhaustive_word_models':{'square_subgroup_words':words_sq,'cross_subgroup_words':words_cross,'Cp_star_Cp_centered_normal_forms_p13_max4syllables':free_product_words},
      'sampled_checks':{'seed':20260909,'linear_junction_pairs':5000,'cactus_subsets':cactus_subsets},
      'nonbacktracking_graphs':nb_summary,
      'numerical_evaluations_not_exact_certificates':numeric,
      'universal_fixed_price':'OPEN',
      'universal_benjamini_schramm':'OPEN',
    }
    output.parent.mkdir(parents=True,exist_ok=True)
    output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--output',type=Path,default=Path(__file__).resolve().parents[1]/'research/artifacts/explicit-window-checks.json')
    main(parser.parse_args().output)
