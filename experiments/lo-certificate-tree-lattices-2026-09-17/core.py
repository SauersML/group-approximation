"""Extract a small unsatisfiable core (certificate) from the SAT instance."""
import sys, pickle
from pysat.solvers import Solver
from bmw import BMW, RATTAGGI_INCOHERENT
from rattaggi_sat import build

def shrink(clauses, name='cadical153'):
    cl = list(clauses)
    for it in range(6):
        nv = max(abs(x) for c in cl for x in c)
        sel = [nv + 1 + i for i in range(len(cl))]
        with Solver(name=name, bootstrap_with=[list(c) + [-s] for c, s in zip(cl, sel)]) as s:
            assert not s.solve(assumptions=sel)
            core = set(s.get_core())
        new = [c for c, sv in zip(cl, sel) if sv in core]
        print("core iteration", it, len(new)); sys.stdout.flush()
        if len(new) == len(cl):
            break
        cl = new
    # deletion-based minimisation
    i = 0
    while i < len(cl):
        trial = cl[:i] + cl[i+1:]
        with Solver(name=name, bootstrap_with=[list(c) for c in trial]) as s:
            if not s.solve():
                cl = trial
                continue
        i += 1
    return cl

if __name__ == "__main__":
    L = int(sys.argv[1]); parity = sys.argv[2] == "lambda"; short = int(sys.argv[3])
    G = BMW(6, 5, RATTAGGI_INCOHERENT)
    els, cb, tb = build(G, L, parity, short)
    # keep triples to map back
    triples = {}
    S = set(els)
    shorts = [g for g in els if len(g[0]) + len(g[1]) <= short]
    for s_ in shorts:
        for q in els:
            for (p, qq) in ((s_, q), (q, s_)):
                r = G.mul(p, qq)
                if r in S:
                    a, b, c = cb.var[p], cb.var[qq], cb.var[r]
                    k = tuple(sorted({-a, -b, c}))
                    if not any(-x in k for x in k):
                        triples.setdefault(k, (p, qq, r))
    mus = shrink(cb.clauses)
    print("MUS size", len(mus))
    out = [triples[c] for c in mus]
    pickle.dump(out, open("core_%s_L%d.pkl" % (sys.argv[2], L), "wb"))
    def fmt(g):
        A, B = g
        s = " ".join(("a%d" % x if x > 0 else "a%d^-1" % -x) for x in A)
        t = " ".join(("b%d" % x if x > 0 else "b%d^-1" % -x) for x in B)
        return "(" + (s + " " + t).strip() + ")"
    for p, q, r in out:
        print(fmt(p), "*", fmt(q), "=", fmt(r))
