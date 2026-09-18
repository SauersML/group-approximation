"""Certificate search in subgroups of Radu's Gamma_{4,4} cut out by abelian invariants.

usage: python3 ab_search.py L SHORT MODE [OUT]
  MODE = derived : elements of [G,G]  (abelianization Z^2/<(2,2),(6,0)> in coordinates (a1,b1))
         c3      : elements of G^+ in ker(psi), psi: a1->1, a2->-1, b1->-1, b2->0 in Z/3
  ball = nontrivial A*B with |A|+|B| <= L lying in the subgroup
"""
import sys, time
from pysat.solvers import Solver
from bmw import make_group
from lo_sat import CNFBuilder
from lo_search import shrink, fmt

AB = {1: (1, 0), -1: (-1, 0), 2: (-1, 0), -2: (1, 0)}          # a-letters
BB = {1: (0, 1), -1: (0, -1), 2: (2, -1), -2: (-2, 1)}         # b-letters

def ab(g):
    x = y = 0
    for i in g[0]:
        x += AB[i][0]; y += AB[i][1]
    for j in g[1]:
        x += BB[j][0]; y += BB[j][1]
    return x, y

def in_derived(g):
    x, y = ab(g)
    return y % 2 == 0 and (x - y) % 6 == 0

def in_c3(g):
    if len(g[0]) % 2 or len(g[1]) % 2:
        return False
    x, y = ab(g)
    return (x - y) % 3 == 0     # psi(a1)=1, psi(b1)=-1 so psi = x - y

if __name__ == "__main__":
    L, short, mode = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    out = sys.argv[4] if len(sys.argv) > 4 else None
    keep = in_derived if mode == "derived" else in_c3
    G = make_group("radu44")
    t0 = time.time()
    els = []
    for la in range(L + 1):
        for lb in range(L + 1 - la):
            if la + lb == 0: continue
            for A in G.reduced_words(G.m, la):
                for B in G.reduced_words(G.n, lb):
                    if keep((A, B)): els.append((A, B))
    S = set(els)
    cb = CNFBuilder(els, G.inv)
    triples = {}
    shorts = [g for g in els if len(g[0]) + len(g[1]) <= short]
    for s_ in shorts:
        for q in els:
            for (p, qq) in ((s_, q), (q, s_)):
                r = G.mul(p, qq)
                if r in S:
                    a, b, c = cb.var[p], cb.var[qq], cb.var[r]
                    k = tuple(sorted({-a, -b, c}))
                    if any(-x in k for x in k): continue
                    if k not in cb.clauses:
                        cb.clauses.add(k); triples[k] = (p, qq, r)
    print("radu44 mode=%s L=%d short=%d elements=%d vars=%d clauses=%d shorts=%d build=%.0fs" % (
        mode, L, short, len(els), cb.nv, len(cb.clauses), len(shorts), time.time() - t0), flush=True)
    with Solver(name='cadical153', bootstrap_with=[list(c) for c in cb.clauses]) as s:
        res = s.solve()
    print("RESULT", "SAT" if res else "UNSAT (not left-orderable)", flush=True)
    if not res and out:
        mus = shrink(cb.clauses)
        with open(out, "w") as f:
            f.write("# non-left-orderability certificate: radu44 subgroup=%s L=%d short=%d\n" % (mode, L, short))
            f.write("# each line p ; q ; r asserts p*q = r; all elements nontrivial and in the subgroup\n")
            for c in mus:
                p, q, r = triples[c]
                f.write("%s ; %s ; %s\n" % (fmt(p), fmt(q), fmt(r)))
        print("minimal certificate triples:", len(mus), "->", out, flush=True)
