"""Certificate for the hypotheses of the rigidity proposition and the m = 2 search.

For each triangle presentation T in tp_q2.json:
  1. check (A1)-(A3) and build the Robertson-Steger 2-graph (checks (H1) uniqueness);
  2. M_1, M_2 have constant row sums 4 and are primitive (exponent printed);
  3. dim_Q H^1(K(Lambda); Q) = 2, where K(Lambda) is the square complex
     (vertices, edges of both colours, one 2-cell per square).  Upper bound via a
     rank over GF(p) (rank_Q >= rank_p), lower bound because d_1, d_2 are independent
     cocycles (a colour-1 cycle has d_1-sum > 0 and d_2-sum 0, and conversely);
  4. the colour-i edges form one class under square transport e ~ e', f ~ f';
  5. the full-domain dimension-2 brick coding SAT instance is UNSAT with two solvers.
"""
import json, sys
import numpy as np
from pysat.solvers import Glucose4
import tp, rs2graph, brick_sat

PR = 1000003


def rank_mod_p(rows, ncols, p=PR):
    """rows: list of dict col->int. Gaussian elimination over GF(p)."""
    pivots = {}
    r = 0
    for row in rows:
        v = {c: x % p for c, x in row.items() if x % p}
        while v:
            c = min(v)
            if c in pivots:
                pr = pivots[c]
                f = v[c]
                for cc, xx in pr.items():
                    v[cc] = (v.get(cc, 0) - f * xx) % p
                    if v[cc] == 0:
                        del v[cc]
            else:
                inv = pow(v[c], p - 2, p)
                pivots[c] = {cc: (xx * inv) % p for cc, xx in v.items()}
                r += 1
                break
    return r


def primitive_exponent(nV, E):
    A = np.zeros((nV, nV), dtype=np.int64)
    for a, b in E:
        A[a, b] = 1
    P = A.copy()
    for k in range(1, 4 * nV * nV):
        if (P > 0).all():
            return k
        P = ((P @ A) > 0).astype(np.int64)
    return None


def one_class(n, pairs):
    par = list(range(n))

    def f(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x
    for a, b in pairs:
        par[f(a)] = f(b)
    return len({f(x) for x in range(n)}) == 1


def main(solve_sat=True):
    ex = json.load(open("tp_q2.json"))["examples"]
    for k, (lam, T, _) in enumerate(ex):
        T = [tuple(t) for t in T]
        tp.check(T, lam)
        tiles, E1, E2, sq = rs2graph.build(T)
        nV, n1, n2 = len(tiles), len(E1), len(E2)
        rows1 = {sum(1 for e in E1 if e[0] == a) for a in range(nV)}
        rows2 = {sum(1 for e in E2 if e[0] == a) for a in range(nV)}
        assert rows1 == {4} and rows2 == {4}
        p1, p2 = primitive_exponent(nV, E1), primitive_exponent(nV, E2)
        assert p1 and p2
        # coboundary D1: C^1 -> C^2 ; D0: C^0 -> C^1 (rank nV - 1 since connected)
        D1 = [{e: 1, n1 + f: 1} for (e, f, f2, e2) in sq]
        for s, (e, f, f2, e2) in enumerate(sq):
            D1[s][n1 + f2] = D1[s].get(n1 + f2, 0) - 1
            D1[s][e2] = D1[s].get(e2, 0) - 1
        r1 = rank_mod_p(D1, n1 + n2)
        r0 = nV - 1
        h1_upper = (n1 + n2 - r1) - r0
        assert h1_upper == 2, h1_upper
        assert one_class(n1, [(s[0], s[3]) for s in sq])
        assert one_class(n2, [(s[1], s[2]) for s in sq])
        print(f"T{k}: lam={lam}; {nV} tiles, {n1}+{n2} edges, {len(sq)} squares; "
              f"row sums 4; primitive exponents {p1},{p2}; dim H^1 = 2; one transport class per colour",
              flush=True)
        if solve_sat:
            for solver in (brick_sat.Cadical153, Glucose4):
                r = brick_sat.solve(T, 2, solver=solver)
                assert r is None
    print("all certificates passed")


if __name__ == "__main__":
    main(solve_sat=(len(sys.argv) < 2 or sys.argv[1] != "nosat"))
