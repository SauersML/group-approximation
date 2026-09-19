"""Exact certificates for positive twisted Alexander rank on 2x2 dead-join Artin groups.

For a representation rho: G -> GL_m(Q) given by permutation or rational matrices, this
script checks, in exact arithmetic over Q (sympy):
  (1) every Artin relation of G holds for rho;
  (2) a nonzero p(t) in Q[t]^m with rho(S_k(uv)) (t rho(u) - 1) p(t) = 0 for all four
      cross edges uv (the reduced criterion of Step 2), found as the kernel of the
      4m x m matrix over Q(t) and cleared of denominators;
  (3) independently of the Step 2 reduction, the full Fox matrix of the whole Artin
      presentation (6 relators x 4 generators, twisted by t^chi rho) has rank < 3m over
      Q(t), i.e. H_1(G; Q(t)^m) != 0; computed exactly with sympy.
Convention: G acts on row vectors on the right, v.g = v t^chi(g) rho(g); Fox derivatives
act by right multiplication; this is H_1(G; M) = Tor(M, Z) for the right module M.
"""
import sys
import sympy as sp

t = sp.symbols('t')


def perm_matrix(p):
    m = len(p)
    M = sp.zeros(m, m)
    # M e_i = e_{p(i)} on columns, so M_{p o q} = M_p M_q (a homomorphism)
    for i in range(m):
        M[p[i], i] = 1
    return M


def S(X, k):
    m = X.shape[0]
    R = sp.eye(m); Q = sp.eye(m)
    for _ in range(k - 1):
        Q = Q * X
        R = R + Q
    return R


def word_mat(w, rho):
    m = next(iter(rho.values())).shape[0]
    R = sp.eye(m)
    for g, s in w:
        R = R * (rho[g] if s == 1 else rho[g].inv())
    return R


def fox(w, x, rho):
    """Fox derivative of word w (list of (gen, +-1)) w.r.t. x, as a matrix via rho."""
    m = next(iter(rho.values())).shape[0]
    D = sp.zeros(m, m)
    prefix = sp.eye(m)
    for g, s in w:
        if s == 1:
            if g == x:
                D += prefix
            prefix = prefix * rho[g]
        else:
            prefix = prefix * rho[g].inv()
            if g == x:
                D -= prefix
    return D


def relators(halves):
    hac, hbc, hbe, hae = halves
    R = [[('a', 1), ('b', 1), ('a', -1), ('b', -1)], [('c', 1), ('e', 1), ('c', -1), ('e', -1)]]
    for (x, y), k in zip([('a', 'c'), ('b', 'c'), ('b', 'e'), ('a', 'e')], halves):
        R.append([(x, 1), (y, 1)] * k + [(x, -1), (y, -1)] * k)
    return R


def certify(halves, rho0, label):
    chi = {'a': 1, 'b': 1, 'c': -1, 'e': -1}
    m = rho0['a'].shape[0]
    print(f"== {label}: halves(ac,bc,be,ae)={halves}, dimension {m}")
    # (1) relations
    ok = True
    for r in relators(halves):
        if word_mat(r, rho0) != sp.eye(m):
            ok = False
    print("(1) all Artin relations hold:", ok)
    # (2) reduced criterion certificate
    A, B, C, E = (rho0[g] for g in 'abce')
    hac, hbc, hbe, hae = halves
    blocks = [S(A * C, hac) * (t * A - sp.eye(m)), S(B * C, hbc) * (t * B - sp.eye(m)),
              S(B * E, hbe) * (t * B - sp.eye(m)), S(A * E, hae) * (t * A - sp.eye(m))]
    Mred = sp.Matrix.vstack(*blocks)
    ns = Mred.nullspace()
    print("(2) dim_Q(t) of {p : S(uv)(tU-1)p = 0 for all cross edges} =", len(ns))
    if ns:
        p = ns[0]
        den = sp.lcm([sp.fraction(sp.together(x))[1] for x in p])
        p = sp.Matrix([sp.factor(sp.together(x * den)) for x in p])
        p = sp.Matrix([sp.expand(x) for x in p])
        print("    certificate p(t) =", list(p))
        print("    check residual zero:", all(sp.expand(x) == 0 for x in (Mred * p)))
    # (3) full Fox matrix rank
    rho = {g: t ** chi[g] * rho0[g] for g in 'abce'}
    rows = []
    for r in relators(halves):
        rows.append(sp.Matrix.hstack(*[fox(r, x, rho) for x in 'abce']))
    d2 = sp.Matrix.vstack(*rows)
    d2 = d2.applyfunc(lambda z: sp.expand(z * t ** 12))  # clear negative powers per row scale
    rk = d2.rank(simplify=True)
    print(f"(3) full Fox matrix: rank d2 = {rk} over Q(t); rank H_1 = {4*m} - {m} - {rk} = {3*m - rk}")
    return len(ns), 3 * m - rk


def signed(d, f):
    """A = I, B = -M_d, C = -I, E = M_f (opposite twos: halves ac = be = 2)."""
    m = len(d)
    return {'a': sp.eye(m), 'b': -perm_matrix(d), 'c': -sp.eye(m), 'e': perm_matrix(f)}


if __name__ == '__main__':
    which = sys.argv[1] if len(sys.argv) > 1 else 'all'
    if which in ('all', 's6'):
        # S_6 witness for opposite twos, halves (2,3,2,4) = labels ac 4, bc 6, be 4, ae 8
        perms = {'a': [0, 1, 2, 3, 4, 5], 'b': [2, 3, 4, 5, 1, 0],
                 'c': [1, 0, 3, 2, 5, 4], 'e': [1, 0, 4, 5, 3, 2]}
        rho = {g: perm_matrix(p) for g, p in perms.items()}
        certify((2, 3, 2, 4), rho, "S_6 permutation rep")
    if which in ('all', 'signed'):
        # signed S_5 witnesses, both odd coprime halves: (2,3,2,5) and (2,5,2,3)
        certify((2, 3, 2, 5), signed([1, 0, 3, 4, 2], [1, 2, 4, 0, 3]), "signed S_5 rep")
        certify((2, 5, 2, 3), signed([1, 2, 3, 4, 0], [1, 0, 4, 2, 3]), "signed S_5 rep")
