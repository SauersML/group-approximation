"""Search a one-vertex complete VH-complex group (or its index-4 parity kernel) for a
non-left-orderability certificate, shrink it to a minimal unsatisfiable set of triples,
and write it in the format read by verify_certificate.py.

usage: python3 lo_search.py GROUP L {full|kernel} SHORT [OUT]
  ball  = nontrivial elements A*B with |A|+|B| <= L (and |A|,|B| even for 'kernel')
  triples = (s, q, s*q) and (q, s, q*s) with |s| <= SHORT, q and the product in the ball
"""
import sys
import time
from pysat.solvers import Solver
from bmw import make_group
from lo_sat import CNFBuilder


def elements(G, L, kernel):
    out = []
    for la in range(0, L + 1):
        for lb in range(0, L + 1 - la):
            if la + lb == 0 or (kernel and (la % 2 or lb % 2)):
                continue
            for A in G.reduced_words(G.m, la):
                for B in G.reduced_words(G.n, lb):
                    out.append((A, B))
    return out


def build(G, L, kernel, short):
    els = elements(G, L, kernel)
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
                    if any(-x in k for x in k):
                        continue
                    if k not in cb.clauses:
                        cb.clauses.add(k)
                        triples[k] = (p, qq, r)
    return els, cb, triples


def shrink(clauses, name='cadical153'):
    cl = list(clauses)
    while True:
        nv = max(abs(x) for c in cl for x in c)
        sel = [nv + 1 + i for i in range(len(cl))]
        with Solver(name=name, bootstrap_with=[list(c) + [-s] for c, s in zip(cl, sel)]) as s:
            assert not s.solve(assumptions=sel)
            core = set(s.get_core())
        new = [c for c, sv in zip(cl, sel) if sv in core]
        print("  core", len(new), flush=True)
        if len(new) >= len(cl) * 0.98:
            cl = new
            break
        cl = new
    i = 0
    while i < len(cl):
        trial = cl[:i] + cl[i + 1:]
        with Solver(name=name, bootstrap_with=[list(c) for c in trial]) as s:
            if not s.solve():
                cl = trial
                continue
        i += 1
    return cl


def fmt(g):
    A, B = g
    s = ["a%d" % x if x > 0 else "a%d^-1" % -x for x in A]
    t = ["b%d" % x if x > 0 else "b%d^-1" % -x for x in B]
    return " ".join(s + t)


if __name__ == "__main__":
    name, L, kernel, short = sys.argv[1], int(sys.argv[2]), sys.argv[3] == "kernel", int(sys.argv[4])
    out = sys.argv[5] if len(sys.argv) > 5 else None
    G = make_group(name)
    t0 = time.time()
    els, cb, triples = build(G, L, kernel, short)
    print("group=%s L=%d %s short=%d elements=%d vars=%d clauses=%d build=%.0fs" % (
        name, L, sys.argv[3], short, len(els), cb.nv, len(cb.clauses), time.time() - t0), flush=True)
    t1 = time.time()
    with Solver(name='cadical153', bootstrap_with=[list(c) for c in cb.clauses]) as s:
        res = s.solve()
    print("RESULT", "SAT (no certificate in this ball)" if res else "UNSAT (not left-orderable)",
          "solve=%.1fs" % (time.time() - t1), flush=True)
    if not res and out:
        mus = shrink(cb.clauses)
        with open(out, "w") as f:
            f.write("# non-left-orderability certificate: group=%s ball L=%d %s short=%d\n" % (name, L, sys.argv[3], short))
            f.write("# each line p ; q ; r asserts p*q = r; all elements nontrivial\n")
            for c in mus:
                p, q, r = triples[c]
                f.write("%s ; %s ; %s\n" % (fmt(p), fmt(q), fmt(r)))
        print("minimal certificate triples:", len(mus), "->", out, flush=True)
