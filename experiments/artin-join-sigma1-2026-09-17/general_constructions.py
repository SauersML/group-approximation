"""Checks of the two general constructions in the classification of 2x2 dead joins
(research/artin-2x2-dead-joins-sigma1-iff-k-q-odd-family-proof.md).

Setup: generators a, b | c, e; [a,b] = [c,e] = 1; cross edge xy with half k:
(xy)^k = (yx)^k; halves listed (h_ac, h_bc, h_be, h_ae); chi = (1,1,-1,-1).
Row vectors, v.g = v t^chi(g) rho(g).  The reduced criterion (Step 2 of the proof):
rank_{F(t)} H_1 = dim { p : S_k(XY)(tX - 1) p = 0 for the four cross edges xy, x in {a,b} }.

Part A (EXACT, sympy over Q(t)): the opposite construction for halves (2, q, 2, p),
3 <= q < p.  Points Z/p, f(i) = i + 1, tau = (0 q), d = tau o f^{-1};
A = I, C = -I, B = -M_d, E = M_f; witness p(t) = -(t M_d + 1)^{-1} (e_1 - e_2).
Checks: all Artin relations (as matrices), the cycle type of d, and that every
reduced block kills p(t).  For small p also the full Fox matrix rank (independent of
the Step 2 reduction), via certify_witness.certify.

Part B (NUMERICAL corroboration, numpy complex128): the vertex construction when the
two halves at e are >= 3:  C = I, A = diag(z1, alpha), B = diag(z2, beta), E with
det E = 1, AE having eigenvalues x1 != x2 (roots of S_{h_ae}) and BE eigenvalues
y1 != y2 (roots of S_{h_be}).  Checks relations, that e_1 is killed by all blocks,
and the generic rank of the full Fox matrix at a random complex t.
Usage: python3 general_constructions.py [A|B|fox|all]
"""
import itertools, sys
import numpy as np
import sympy as sp
from certify_witness import perm_matrix, S, relators, word_mat, certify

t = sp.symbols('t')


def cycle_type(p):
    m = len(p); seen = [False] * m; ct = []
    for i in range(m):
        if not seen[i]:
            j = i; c = 0
            while not seen[j]:
                seen[j] = True; j = p[j]; c += 1
            ct.append(c)
    return tuple(sorted(ct))


def opposite_rep(q, p):
    f = [(i + 1) % p for i in range(p)]
    finv = [(i - 1) % p for i in range(p)]
    tau = list(range(p)); tau[0], tau[q] = q, 0
    d = [tau[finv[i]] for i in range(p)]
    rho = {'a': sp.eye(p), 'b': -perm_matrix(d), 'c': -sp.eye(p), 'e': perm_matrix(f)}
    return d, f, tau, rho


def part_A(qmax=9):
    ok_all = True
    for p in range(4, qmax + 1):
        for q in range(3, p):
            halves = (2, q, 2, p)
            d, f, tau, rho = opposite_rep(q, p)
            rel = all(word_mat(r, rho) == sp.eye(p) for r in relators(halves))
            ct_ok = cycle_type(d) == tuple(sorted((q, p - q)))
            A, B, C, E = (rho[g] for g in 'abce')
            v = sp.zeros(p, 1); v[1] = 1; v[2] = -1
            Md = perm_matrix(d)
            w = -(t * Md + sp.eye(p)).LUsolve(v)
            blocks = [S(A * C, 2) * (t * A - sp.eye(p)), S(B * C, q) * (t * B - sp.eye(p)),
                      S(B * E, 2) * (t * B - sp.eye(p)), S(A * E, p) * (t * A - sp.eye(p))]
            kill = all(sp.simplify(x) == 0 for Bk in blocks for x in (Bk * w))
            nonzero = any(sp.simplify(x) != 0 for x in w)
            ok = rel and ct_ok and kill and nonzero
            ok_all &= ok
            print(f"A (2,{q},2,{p}) dim {p}: relations {rel}; d cycle type {cycle_type(d)} ok {ct_ok}; "
                  f"p(t) != 0 {nonzero}; all blocks kill p(t) {kill}", flush=True)
    # q = 2 must fail (K_q family): the witness is not killed by the be block
    for p in (3, 5):
        d, f, tau, rho = opposite_rep(2, p)
        A, B, C, E = (rho[g] for g in 'abce')
        v = sp.zeros(p, 1); v[1] = 1; v[2] = -1
        Mred = sp.Matrix.vstack(S(A * C, 2) * (t * A - sp.eye(p)), S(B * C, 2) * (t * B - sp.eye(p)),
                                S(B * E, 2) * (t * B - sp.eye(p)), S(A * E, p) * (t * A - sp.eye(p)))
        print(f"A control q=2, (2,2,2,{p}): dim of reduced kernel = {len(Mred.nullspace())} (expected 0)")
    print("PART A ALL OK:", ok_all)


def roots_S(h):
    return [np.exp(2j * np.pi * k / h) for k in range(1, h)]


def npS(X, k):
    R = np.eye(X.shape[0], dtype=complex); Q = R.copy()
    for _ in range(k - 1):
        Q = Q @ X; R = R + Q
    return R


def vertex_rep(halves):
    hac, hbc, hbe, hae = halves
    for z1 in roots_S(hac):
        for z2 in roots_S(hbc):
            for x1, x2 in itertools.combinations(roots_S(hae), 2):
                for y1, y2 in itertools.combinations(roots_S(hbe), 2):
                    if abs(z1 ** 2 * y1 * y2 - z2 ** 2 * x1 * x2) < 1e-6:
                        continue
                    al, be = x1 * x2 / z1, y1 * y2 / z2
                    M = np.array([[z1, al], [z2, be]])
                    e11, e22 = np.linalg.solve(M, [x1 + x2, y1 + y2])
                    E = np.array([[e11, 1], [e11 * e22 - 1, e22]])
                    return {'a': np.diag([z1, al]), 'b': np.diag([z2, be]), 'c': np.eye(2), 'e': E}
    return None


def np_word(w, rho):
    R = np.eye(2, dtype=complex)
    for g, s in w:
        R = R @ (rho[g] if s == 1 else np.linalg.inv(rho[g]))
    return R


def np_fox_rank(halves, rho0, t0):
    chi = {'a': 1, 'b': 1, 'c': -1, 'e': -1}
    rho = {g: t0 ** chi[g] * rho0[g] for g in 'abce'}
    m = 2
    rows = []
    for r in relators(halves):
        blocks = []
        for x in 'abce':
            D = np.zeros((m, m), dtype=complex); pre = np.eye(m, dtype=complex)
            for g, s in r:
                if s == 1:
                    if g == x:
                        D += pre
                    pre = pre @ rho[g]
                else:
                    pre = pre @ np.linalg.inv(rho[g])
                    if g == x:
                        D -= pre
            blocks.append(D)
        rows.append(np.hstack(blocks))
    return np.linalg.matrix_rank(np.vstack(rows), tol=1e-8)


def part_B(hmax=6):
    rng = np.random.default_rng(1)
    ok_all = True
    count = 0
    for halves in itertools.product(range(2, hmax + 1), range(2, hmax + 1),
                                    range(3, hmax + 1), range(3, hmax + 1)):
        if halves == (2, 2, 3, 3):
            continue
        rho = vertex_rep(halves)
        if rho is None:
            print("B no choice found for", halves); ok_all = False; continue
        rel = all(np.allclose(np_word(r, rho), np.eye(2), atol=1e-8) for r in relators(halves))
        hac, hbc, hbe, hae = halves
        A, B, C, E = (rho[g] for g in 'abce')
        t0 = complex(rng.normal(), rng.normal())
        e1 = np.array([1, 0])
        blocks = [npS(A @ C, hac) @ (t0 * A - np.eye(2)), npS(B @ C, hbc) @ (t0 * B - np.eye(2)),
                  npS(B @ E, hbe) @ (t0 * B - np.eye(2)), npS(A @ E, hae) @ (t0 * A - np.eye(2))]
        kill = all(np.allclose(Bk @ e1, 0, atol=1e-8) for Bk in blocks)
        rk = np_fox_rank(halves, rho, t0)
        ok = rel and kill and (6 - rk) >= 1
        ok_all &= ok
        count += 1
        if not ok:
            print("B FAIL", halves, rel, kill, rk)
    print(f"B vertex construction, {count} halves with h_ac,h_bc in 2..{hmax}, h_be,h_ae in 3..{hmax} "
          f"except (2,2,3,3): relations, e_1 killed, Fox rank H_1 >= 1 at random t: ALL OK = {ok_all}")
    print("B (2,2,3,3): vertex_rep finds a choice:", vertex_rep((2, 2, 3, 3)) is not None,
          "(expected False: the pair products are forced equal)")
    w = np.exp(2j * np.pi / 3)
    one = {'a': np.eye(2), 'b': np.eye(2), 'c': -np.eye(2), 'e': w * np.eye(2)}
    print("B (2,2,3,3) scalar witness a=b=1, c=-1, e=omega (doubled): Fox rank H_1 at random t =",
          6 - np_fox_rank((2, 2, 3, 3), one, complex(0.7, 0.3)), "(expected 2)")


if __name__ == '__main__':
    which = sys.argv[1] if len(sys.argv) > 1 else 'all'
    if which in ('A', 'all'):
        part_A()
    if which in ('B', 'all'):
        part_B()
    if which in ('fox', 'all'):
        for q, p in [(3, 4), (3, 5), (4, 5)]:
            d, f, tau, rho = opposite_rep(q, p)
            certify((2, q, 2, p), rho, f"general opposite construction d={d}, f={f}")
