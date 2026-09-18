#!/usr/bin/env python3
"""Independent exact verifier (sympy; shares no code with the search) of a rank-(2,4) bowtie certificate in [1,c]_W,
c = s_1 ... s_n.  Certificates are written by rank24_bowties.py with CERT_OUT=...

Usage: verify_bowtie24.py cert.json

Checks:
  (1) each witness (f, S2, S4) is a sequence f of n real roots with s_f1 ... s_fn = c (so it is reduced, lemma M0),
      with S2 a 2-subset of the 4-subset S4.  By the subword lemma the S2-subword product lies below the S4-subword
      product, which is a coatom of [1,c]_W;
  (2) the two u-witnesses give the same coatom u, with S2-products x and y; the two v-witnesses give the same x, y and
      a coatom v; x != y, u != v;
  (3) U = Mov(x) + Mov(y) has dimension 3 and det(E^T B (1-c)^{-1} E) <= 0 for a basis E of U.
Lemma D of the proof gives det chi_c|Mov(z) > 0 for every z in [1,c]_W, and a rank-3 z above x and y has Mov(z) = U.
So no rank-3 element lies above x and y, u and v are distinct minimal upper bounds, and [1,c]_W is not a lattice.
"""
import sys, json
import sympy as sp

PHI = (1 + sp.sqrt(5)) / 2

def main():
    C = json.load(open(sys.argv[1]))
    n = C['n']
    Bm = sp.eye(n)
    for i, j, m in C['edges']:
        Bm[i, j] = Bm[j, i] = -sp.cos(sp.pi / m)
    def B(x, y): return sp.radsimp(sp.expand((x.T * Bm * y)[0, 0]))
    def refl(r): return sp.expand(sp.eye(n) - 2 * r * (r.T * Bm))
    def vec(t): return sp.Matrix([sp.Integer(x[0]) + sp.Integer(x[1]) * PHI for x in t])
    def simple(i):
        e = sp.zeros(n, 1); e[i] = 1; return e
    def is_root(r, cap=10000):
        if sp.simplify(B(r, r) - 1) != 0: return False
        if all(sp.simplify(x) <= 0 for x in r): r = -r
        for _ in range(cap):
            cs = [sp.simplify(x) for x in r]
            if any(x < 0 for x in cs): return False
            nz = [i for i in range(n) if cs[i] != 0]
            if len(nz) == 1 and cs[nz[0]] == 1: return True
            for i in range(n):
                if sp.simplify(B(r, simple(i))) > 0:
                    r = refl(simple(i)) * r; break
            else:
                return False
        raise RuntimeError('descent cap reached')
    def prod(rs):
        g = sp.eye(n)
        for r in rs: g = g * refl(r)
        return sp.expand(g)
    def same(X, Y): return all(sp.simplify(x - y) == 0 for x, y in zip(X, Y))
    c = prod([simple(i) for i in range(n)])
    tops, lows = [], []
    for key in ('u_witnesses', 'v_witnesses'):
        ts, ls = [], []
        for f, S2, S4 in C[key]:
            fr = [vec(t) for t in f]
            assert len(fr) == n and len(S4) == 4 and len(S2) == 2 and set(S2) <= set(S4)
            assert all(is_root(r) for r in fr), 'witness letter is not a real root'
            assert same(prod(fr), c), 'witness factorization does not multiply to c'
            ts.append(prod([fr[i] for i in sorted(S4)]))
            ls.append((prod([fr[i] for i in sorted(S2)]), [fr[i] for i in sorted(S2)]))
        assert same(ts[0], ts[1]), 'two witnesses give different coatoms'
        tops.append(ts[0]); lows.append(ls)
    x, y = lows[0][0][0], lows[0][1][0]
    assert same(x, lows[1][0][0]) and same(y, lows[1][1][0]), 'u- and v-witnesses give different x, y'
    assert not same(x, y), 'x = y'
    assert not same(tops[0], tops[1]), 'u = v'
    E = sp.Matrix.hstack(*(lows[0][0][1] + lows[0][1][1]))
    assert E.rank() == 3, 'dim Mov(x) + Mov(y) != 3'
    cols = []
    for j in range(4):
        if sp.Matrix.hstack(*(cols + [E[:, j]])).rank() > len(cols): cols.append(E[:, j])
    E3 = sp.Matrix.hstack(*cols)
    print(f"[{C['group']}] witnesses verified: x, y <= u and x, y <= v in [1,c]_W, x != y, u != v, dim(Mov x + Mov y) = 3")
    d = sp.radsimp(sp.simplify((E3.T * Bm * (sp.eye(n) - c).inv() * E3).det()))
    print(f'  det chi_c|(Mov x + Mov y) = {d} ~ {sp.N(d, 8)}')
    if sp.simplify(d) <= 0:
        print('  CERTIFIED: no rank-3 element above x, y (Lemma D); (x, y; u, v) is a bowtie; [1,c]_W is not a lattice')
        return 0
    print('  NOT CERTIFIED: det > 0')
    sys.exit(1)

if __name__ == '__main__':
    main()
