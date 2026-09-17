"""Certificate search inside the normal closure N of given elements of a BMW group.

usage: python3 ncl_search.py GROUP R LEVELS [OUT]
  L1 = conjugates g x g^-1 of x in {c, c^-1, d, d^-1}, g in the ball |A|+|B| <= R,
       where c = [a1^3, a2^4], d = [a2^3, a1^4]  (x^-1 y^-1 x y)
  E  = L1 u L1*L1 (LEVELS=2)
  triples (p, q, p*q) with p in L1, q in E and p*q in E (both orders).
Every element of E lies in N, so UNSAT proves N is not left-orderable.
"""
import sys
import time
from pysat.solvers import Solver
from bmw import make_group
from lo_sat import CNFBuilder
from lo_search import shrink, fmt


def word(G, s):
    g = ((), ())
    for tok in s.split():
        base, _, e = tok.partition("^")
        e = int(e) if e else 1
        i = int(base[1:])
        x = G.gen_a(i) if base[0] == "a" else G.gen_b(i)
        if e < 0:
            x = G.inv(x)
        for _ in range(abs(e)):
            g = G.mul(g, x)
    return g


def comm(G, x, y):
    return G.mul(G.mul(G.inv(x), G.inv(y)), G.mul(x, y))


def ball(G, R):
    out = []
    for la in range(R + 1):
        for lb in range(R + 1 - la):
            for A in G.reduced_words(G.m, la):
                for B in G.reduced_words(G.n, lb):
                    out.append((A, B))
    return out


if __name__ == "__main__":
    name, R, levels = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    out = sys.argv[4] if len(sys.argv) > 4 else None
    G = make_group(name)
    t0 = time.time()
    a1, a2 = word(G, "a1"), word(G, "a2")
    pw = lambda x, k: word(G, "") if k == 0 else G.mul(pw(x, k - 1), x)
    c = comm(G, pw(a1, 3), pw(a2, 4))
    d = comm(G, pw(a2, 3), pw(a1, 4))
    print("c =", fmt(c), " d =", fmt(d))
    gens = [c, G.inv(c), d, G.inv(d)]
    L1 = set()
    for g in ball(G, R):
        gi = G.inv(g)
        for x in gens:
            L1.add(G.mul(G.mul(g, x), gi))
    L1.discard(((), ()))
    L1 = sorted(L1)
    E = set(L1)
    if levels >= 2:
        for p in L1:
            for q in L1:
                E.add(G.mul(p, q))
    E.discard(((), ()))
    E = sorted(E)
    Es = set(E)
    cb = CNFBuilder(E, G.inv)
    triples = {}
    for p in L1:
        for q in E:
            for (x, y) in ((p, q), (q, p)):
                r = G.mul(x, y)
                if r in Es:
                    a, b, cc = cb.var[x], cb.var[y], cb.var[r]
                    k = tuple(sorted({-a, -b, cc}))
                    if any(-z in k for z in k):
                        continue
                    if k not in cb.clauses:
                        cb.clauses.add(k)
                        triples[k] = (x, y, r)
    print("group=%s R=%d levels=%d L1=%d elements=%d vars=%d clauses=%d build=%.0fs" % (
        name, R, levels, len(L1), len(E), cb.nv, len(cb.clauses), time.time() - t0), flush=True)
    t1 = time.time()
    with Solver(name='cadical153', bootstrap_with=[list(k) for k in cb.clauses]) as s:
        res = s.solve()
    print("RESULT", "SAT (no certificate)" if res else "UNSAT (normal closure not left-orderable)",
          "solve=%.1fs" % (time.time() - t1), flush=True)
    if not res and out:
        mus = shrink(cb.clauses)
        with open(out, "w") as f:
            f.write("# non-left-orderability certificate for the normal closure of [a1^3,a2^4], [a2^3,a1^4]: group=%s R=%d levels=%d\n" % (name, R, levels))
            f.write("# each line p ; q ; r asserts p*q = r; all elements nontrivial and in the normal closure\n")
            for k in mus:
                p, q, r = triples[k]
                f.write("%s ; %s ; %s\n" % (fmt(p), fmt(q), fmt(r)))
        print("minimal certificate triples:", len(mus), "->", out, flush=True)
