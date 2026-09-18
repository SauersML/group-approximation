#!/usr/bin/env python3
"""Independent exact verifier (sympy, sqrt5 arithmetic; shares no code with the search) of a rank-(1,3) bowtie
certificate in the noncrossing partition poset [1,c]_W, c = s_1 ... s_n, any rank n >= 4.

Usage: verify_bowtie.py cert.json          (certificates are written by rank3_bowties.py with CERT_OUT=...)

Checks:
  (1) each of the four witnesses (f, S) is a sequence f of n real roots (B(r,r) = 1, root descent reaches a simple
      root) with s_f1 ... s_fn = c.  Such a factorization is reduced (lemma M0), so the subword product
      prod_{i in S} s_fi lies in [1,c]_W with rank |S| = 3 and every letter of the subword lies below it;
  (2) the two p-witness subwords have the same product p and contain alpha_a resp. alpha_b; same for q; p != q;
  (3) det( E^T B (1-c)^{-1} E ) <= 0 for E = [alpha_a, alpha_b].
Lemma D (proved in the claim's -proof.md): every rank-2 element z of [1,c]_W has det chi_c|Mov(z) > 0, and a rank-2
z above a and b has Mov(z) = span(alpha_a, alpha_b).  Hence no rank-2 element lies above a and b, nothing lies
strictly between {a, b} and {p, q}, the join of a and b does not exist, and [1,c]_W is not a lattice.
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
    a, b = vec(C['alpha_a']), vec(C['alpha_b'])
    tops = []
    for key in ('p_witnesses', 'q_witnesses'):
        prods = []
        for (f, S), letter in zip(C[key], (a, b)):
            fr = [vec(t) for t in f]
            assert len(fr) == n and len(S) == 3
            assert all(is_root(r) for r in fr), 'witness letter is not a real root'
            assert same(prod(fr), c), 'witness factorization does not multiply to c'
            assert any(same(fr[i], letter) for i in S), 'letter not in subword'
            prods.append(prod([fr[i] for i in S]))
        assert same(prods[0], prods[1]), 'two subwords give different elements'
        tops.append(prods[0])
    assert not same(tops[0], tops[1]), 'p = q'
    print(f"[{C['group']}] witnesses verified: a, b <= p and a, b <= q in [1,c]_W, p != q, rank(p) = rank(q) = 3")
    E = a.row_join(b)
    M = E.T * Bm * (sp.eye(n) - c).inv() * E
    d = sp.radsimp(sp.simplify(M.det()))
    print(f'  B(alpha_a, alpha_b) = {sp.radsimp(B(a, b))} ~ {sp.N(B(a, b), 8)};  det chi_c|span(alpha_a, alpha_b) = {d} ~ {sp.N(d, 8)}')
    if sp.simplify(d) <= 0:
        print('  CERTIFIED: no rank-2 element above a, b (Lemma D); (a, b; p, q) is a bowtie; [1,c]_W is not a lattice')
        return 0
    print('  NOT CERTIFIED: det > 0')
    sys.exit(1)

if __name__ == '__main__':
    main()
