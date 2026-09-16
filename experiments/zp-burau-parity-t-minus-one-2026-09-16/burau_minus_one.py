#!/usr/bin/env python3
"""Exact check: an explicit nontrivial Brunnian 4-braid whose Burau matrix is
congruent to the identity modulo (t+1).

Conventions (as in research/zaremsky-3-05-four-strand-burau-faithful.md):
unreduced Burau rho_n(sigma_i) = I_{i-1} (+) [[1-t, t],[1, 0]] (+) I_{n-i-1}
over Z[t, t^{-1}].  A braid word is a list of nonzero ints: +i = sigma_i,
-i = sigma_i^{-1}.

Laurent polynomials are dicts {exponent: nonzero int}; everything is exact
integer arithmetic.  A matrix over Z[t^{+-1}] is congruent to I mod (t+1)
iff it evaluates to I at t = -1, because Z[t^{+-1}]/(t+1) = Z via t -> -1.

Checks performed (all must print True):
 1. rho_4 satisfies the braid relations and sigma_i sigma_i^{-1} = 1
    (sanity of the implementation);
 2. the transpose identity rho(sigma_i)^T = D rho(sigma_i) D^{-1} with
    D = diag(1, t, t^2, t^3) (used for convention independence);
 3. T2 := (sigma_1 sigma_2)^6 has rho_4(T2)(-1) = I and rho_4(T2) != I;
 4. b := [A14, [A24, A34]] is Brunnian (strand-forgetting on the Artin
    action, a control) and nontrivial;
 5. Phi0 := [T2, b] has rho_4(Phi0) != I over Z[t^{+-1}] (so Phi0 != 1 in
    B_4) and rho_4(Phi0)(-1) = I;
 6. the Fox Jacobian at t = -1 of the Artin automorphism of Phi0 is I for
    both handedness conventions and both composition orders (the
    homological action of Phi0 on H_1 of the Z-cover relative to the lifted
    base point, specialised at t = -1);
 7. the mirror image iota(Phi0) and the reversed word rev(Phi0) also have
    identity Burau matrix at t = -1.
"""
import sys

# ---------- Laurent polynomials ----------

def padd(p, q, s=1):
    r = dict(p)
    for e, c in q.items():
        v = r.get(e, 0) + s * c
        if v:
            r[e] = v
        else:
            r.pop(e, None)
    return r

def pmul(p, q):
    r = {}
    for e1, c1 in p.items():
        for e2, c2 in q.items():
            e = e1 + e2
            v = r.get(e, 0) + c1 * c2
            if v:
                r[e] = v
            else:
                r.pop(e, None)
    return r

def peval_m1(p):
    return sum(c * (-1) ** (e % 2) for e, c in p.items())

ONE = {0: 1}
ZERO = {}

def mmul(A, B):
    n = len(A)
    C = [[{} for _ in range(n)] for _ in range(n)]
    for i in range(n):
        for k in range(n):
            if not A[i][k]:
                continue
            for j in range(n):
                if B[k][j]:
                    C[i][j] = padd(C[i][j], pmul(A[i][k], B[k][j]))
    return C

def ident(n):
    return [[dict(ONE) if i == j else {} for j in range(n)] for i in range(n)]

def is_ident(A):
    n = len(A)
    return all(A[i][j] == (ONE if i == j else ZERO) for i in range(n) for j in range(n))

def eval_m1(A):
    return [[peval_m1(x) for x in row] for row in A]

def transpose(A):
    n = len(A)
    return [[A[j][i] for j in range(n)] for i in range(n)]

def gen(n, s):
    """rho_n(sigma_i^{+-1})."""
    i = abs(s) - 1
    M = ident(n)
    if s > 0:
        blk = [[{0: 1, 1: -1}, {1: 1}], [{0: 1}, {}]]
    else:  # inverse of [[1-t, t],[1,0]] is [[0, 1],[t^{-1}, 1 - t^{-1}]]
        blk = [[{}, {0: 1}], [{-1: 1}, {0: 1, -1: -1}]]
    for a in range(2):
        for c in range(2):
            M[i + a][i + c] = blk[a][c]
    return M

def rho(n, word):
    M = ident(n)
    for s in word:
        M = mmul(M, gen(n, s))
    return M

# ---------- braid words ----------

def inv(w):
    return [-s for s in reversed(w)]

def comm(x, y):
    return x + y + inv(x) + inv(y)

def A(i, j):
    """A_{ij} = sigma_{j-1} ... sigma_{i+1} sigma_i^2 sigma_{i+1}^{-1} ... sigma_{j-1}^{-1}."""
    c = list(range(j - 1, i, -1))
    return c + [i, i] + inv(c)

# ---------- free group / Artin action ----------

def freduce(w):
    out = []
    for x in w:
        if out and out[-1] == -x:
            out.pop()
        else:
            out.append(x)
    return out

def artin_gen(n, s, hand):
    """Automorphism of F_n (as dict j -> word) for sigma_{|s|}^{sign s}.
    hand = +1: A_i: x_i -> x_i x_{i+1} x_i^{-1}, x_{i+1} -> x_i.
    hand = -1: the inverse automorphism A_i^{-1}.  Letters: +j = x_j."""
    i = abs(s)
    e = (1 if s > 0 else -1) * hand
    h = {j: [j] for j in range(1, n + 1)}
    if e > 0:
        h[i] = [i, i + 1, -i]
        h[i + 1] = [i]
    else:
        h[i] = [i + 1]
        h[i + 1] = [-(i + 1), i, i + 1]
    return h

def apply(h, w):
    out = []
    for x in w:
        out.extend(h[x] if x > 0 else inv(h[-x]))
    return freduce(out)

def compose(h, g):
    """(h o g)(x_j) = h(g(x_j))."""
    return {j: apply(h, g[j]) for j in g}

def artin(n, word, hand, order):
    h = {j: [j] for j in range(1, n + 1)}
    for s in word:
        a = artin_gen(n, s, hand)
        h = compose(h, a) if order == 0 else compose(a, h)
    return h

def fox_jacobian_m1(h, n):
    """J[j][k] = phi(d h(x_j) / d x_k) at t = -1, phi(x_i) = t."""
    J = [[0] * n for _ in range(n)]
    for j in range(1, n + 1):
        e = 0
        for x in h[j]:
            k = abs(x)
            if x > 0:
                J[j - 1][k - 1] += (-1) ** (e % 2)
                e += 1
            else:
                e -= 1
                J[j - 1][k - 1] -= (-1) ** (e % 2)
    return J

def forget(n, h, j):
    """Kill x_j and renumber; valid for pure braids (h(x_j) conjugate of x_j)."""
    ren = {}
    c = 0
    for i in range(1, n + 1):
        if i != j:
            c += 1
            ren[i] = c
    def kill(w):
        return freduce([(1 if x > 0 else -1) * ren[abs(x)] for x in w if abs(x) != j])
    return {ren[i]: kill(h[i]) for i in h if i != j}

def is_id_aut(h):
    return all(h[j] == [j] for j in h)

def mirror(w):
    return [-s for s in w]

def main():
    n = 4
    ok = True
    # 1. relations
    r1 = is_ident(rho(n, [1, -1])) and is_ident(rho(n, [-2, 2]))
    r2 = rho(n, [1, 2, 1]) == rho(n, [2, 1, 2]) and rho(n, [2, 3, 2]) == rho(n, [3, 2, 3])
    r3 = rho(n, [1, 3]) == rho(n, [3, 1])
    print("1. braid relations hold for rho_4:", r1 and r2 and r3)
    ok &= r1 and r2 and r3
    # 2. transpose identity
    D = [[{k: 1} if a == b else {} for b in range(n)] for a, k in zip(range(n), range(n))]
    Dinv = [[{-k: 1} if a == b else {} for b in range(n)] for a, k in zip(range(n), range(n))]
    tr = all(transpose(gen(n, i)) == mmul(mmul(D, gen(n, i)), Dinv) for i in (1, 2, 3))
    print("2. rho(sigma_i)^T = D rho(sigma_i) D^-1:", tr)
    ok &= tr
    # 3. T2
    T2 = [1, 2] * 6
    RT2 = rho(n, T2)
    c3 = eval_m1(RT2) == [[int(i == j) for j in range(n)] for i in range(n)] and not is_ident(RT2)
    print("3. rho_4((s1 s2)^6) = I at t=-1 and != I:", c3)
    ok &= c3
    # 4. b Brunnian
    b = comm(A(1, 4), comm(A(2, 4), A(3, 4)))
    hb = artin(n, b, 1, 0)
    brun = all(is_id_aut(forget(n, hb, j)) for j in range(1, n + 1))
    print("4. b = [A14,[A24,A34]]: length", len(b), "; forgetting any strand trivial:", brun,
          "; nontrivial:", not is_id_aut(hb))
    ok &= brun and not is_id_aut(hb)
    # 5. Phi0
    Phi0 = comm(T2, b)
    R = rho(n, Phi0)
    I4 = [[int(i == j) for j in range(n)] for i in range(n)]
    c5 = (not is_ident(R)) and eval_m1(R) == I4
    print("5. Phi0 = [T2, b]: length", len(Phi0), "; rho_4(Phi0) != I:", not is_ident(R),
          "; rho_4(Phi0)(-1) = I:", eval_m1(R) == I4)
    hP = artin(n, Phi0, 1, 0)
    brunP = all(is_id_aut(forget(n, hP, j)) for j in range(1, n + 1))
    print("   Phi0 Brunnian (control via Artin action):", brunP)
    ok &= c5 and brunP
    maxdeg = max(max(e for e in x) for row in R for x in row if x)
    mindeg = min(min(e for e in x) for row in R for x in row if x)
    print("   exponent range of rho_4(Phi0) entries:", mindeg, maxdeg)
    # 6. Fox Jacobians
    c6 = True
    for hand in (1, -1):
        for order in (0, 1):
            h = artin(n, Phi0, hand, order)
            J = fox_jacobian_m1(h, n)
            c6 &= (J == I4)
            print("6. hand", hand, "order", order, ": Fox Jacobian at -1 is I:", J == I4,
                  "; automorphism nontrivial:", not is_id_aut(h))
            c6 &= not is_id_aut(h)
    ok &= c6
    # 7. mirror and reverse
    c7 = eval_m1(rho(n, mirror(Phi0))) == I4 and eval_m1(rho(n, list(reversed(Phi0)))) == I4
    print("7. mirror and reversed word also = I at t=-1:", c7)
    ok &= c7
    print("ALL CHECKS PASS:", ok)
    print("Phi0 word:", " ".join(str(s) for s in Phi0))
    return 0 if ok else 1

if __name__ == "__main__":
    sys.exit(main())
