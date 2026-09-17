#!/usr/bin/env python3
"""Exact checks for research/clean-moody-counts-are-blind-at-every-evaluation-point.

Unreduced Burau rho_n(sigma_i) = I (+) [[1-t, t],[1, 0]] (+) I over Z[t^{+-1}];
words are lists of nonzero ints (+i = sigma_i, -i = sigma_i^{-1}).  Laurent
polynomials are dicts {exponent: int}; all arithmetic is exact.  The helper
block (Laurent arithmetic, rho, Artin action, strand forgetting) is copied from
experiments/zp-burau-parity-t-minus-one-2026-09-16/burau_minus_one.py.

A matrix R is congruent to I modulo a monic g in Z[t] (g(0) != 0) iff every
entry of R - I, multiplied by a power of t, is divisible by g in Z[t]
(t is a unit mod g, and monic division is exact over Z).

Checks:
 1. braid relations for rho_4;
 2. rho(sigma_1^2) = I + (t-1)N with N^2 = (1+t)N; rho((s1 s2)^3) = I + (t-1)N'
    with N'^2 = (1+t+t^2)N'; the resulting power congruences for j <= 6, and
    sharpness (sigma_1^6 not = I mod Phi_2, Delta_3^6 not = I mod Phi_3);
 3. b = [A14,[A24,A34]] is Brunnian, and rho_4(b) = I mod (t-1)^2, != I;
 4. Psi_q = [X_q, b] (X_q a twist power) has rho_4(Psi_q) = I mod Phi_q,
    rho_4(Psi_q) != I, and is pure, for q = 2..24.  (Psi_q is Brunnian by
    normality of Brun_4; the Artin-action control of burau_minus_one.py is
    infeasible here: image words of Psi_2 already have ~10^6 letters.);
 5. iterated commutators realise product ideals (jets);
 6. calibration in B_3; 7. the reduced 3x3 matrix N' of check 2 is printed.
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


# ---------- cyclotomic congruences ----------

def cyclotomic(q):
    """Phi_q as a coefficient list (low -> high), via t^q - 1 = prod_{d | q} Phi_d."""
    num = [-1] + [0] * (q - 1) + [1]
    for d in range(1, q):
        if q % d == 0:
            num = pdivexact(num, cyclotomic(d))
    return num

def pdivmod(a, g):
    """Divide integer polynomial a by monic g (coefficient lists, low -> high)."""
    a = list(a)
    dg = len(g) - 1
    assert g[-1] == 1
    if len(a) - 1 < dg:
        return [0], a
    qt = [0] * (len(a) - dg)
    for k in range(len(a) - 1, dg - 1, -1):
        c = a[k]
        if c:
            qt[k - dg] = c
            for i in range(dg + 1):
                a[k - dg + i] -= c * g[i]
    return qt, a[:dg] if dg > 0 else [0]

def pdivexact(a, g):
    qt, r = pdivmod(a, g)
    assert all(x == 0 for x in r), "not divisible"
    return qt

def plist_mul(a, b):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            r[i + j] += x * y
    return r

def laurent_to_list(p):
    """Laurent dict -> coefficient list after multiplying by t^{-min exponent}."""
    if not p:
        return [0]
    lo = min(p)
    hi = max(p)
    return [p.get(e, 0) for e in range(lo, hi + 1)]

def divisible(p, g):
    if not p:
        return True
    _, r = pdivmod(laurent_to_list(p), g)
    return all(x == 0 for x in r)

def minus_ident(R):
    n = len(R)
    return [[padd(R[i][j], ONE, -1) if i == j else R[i][j] for j in range(n)] for i in range(n)]

def congruent_to_I(R, g):
    D = minus_ident(R)
    return all(divisible(x, g) for row in D for x in row)

def rho_at_one_is_I(R):
    """rho(w)(1) is the permutation matrix of w; = I iff w is pure."""
    n = len(R)
    return all(sum(R[i][j].values()) == int(i == j) for i in range(n) for j in range(n))

def power(w, j):
    return w * j if j >= 0 else inv(w) * (-j)

def brunnian_control(n, w):
    h = artin(n, w, 1, 0)
    return (not is_id_aut(h)) and all(is_id_aut(forget(n, h, j)) for j in range(1, n + 1))

T3 = [1, 2] * 3          # Delta_3^2 = T_c, Dehn twist about a curve around p1,p2,p3
S12 = [1, 1]             # A_12 = sigma_1^2, Dehn twist about a curve around p1,p2

def twist_for(q):
    """A twist power X with rho_4(X) = I mod Phi_q (q >= 2)."""
    if q == 2:
        return power(T3, 2)                      # (t^6-1)/(t^2+t+1) = (t-1)(t^3+1)
    return power(S12, q // 2 if q % 2 == 0 else q)  # (t^{2j}-1)/(t+1)

def main():
    n = 4
    ok = True
    I4 = [[int(i == j) for j in range(n)] for i in range(n)]
    r = (is_ident(rho(n, [1, -1])) and rho(n, [1, 2, 1]) == rho(n, [2, 1, 2])
         and rho(n, [2, 3, 2]) == rho(n, [3, 2, 3]) and rho(n, [1, 3]) == rho(n, [3, 1]))
    print("1. braid relations for rho_4:", r); ok &= r

    # 2. twist structure: rho(X) = I + (t-1) N with N^2 = c N
    for name, w, c in (("sigma_1^2", S12, {0: 1, 1: 1}), ("(s1 s2)^3", T3, {0: 1, 1: 1, 2: 1})):
        D = minus_ident(rho(n, w))
        N = [[{e: v for e, v in zip(range(min(x) if x else 0, 10**9),
                                     pdivexact(laurent_to_list(x), [-1, 1])) if v}
              if x else {} for x in row] for row in D]
        back = [[pmul({0: -1, 1: 1}, x) for x in row] for row in N]
        NN = mmul(N, N)
        cN = [[pmul(c, x) for x in row] for row in N]
        good = back == D and NN == cN
        print("2.", name, ": rho - I = (t-1)N and N^2 = c N:", good); ok &= good
    for j in range(1, 7):
        g1 = pdivexact([-1] + [0] * (2 * j - 1) + [1], [1, 1])
        g2 = pdivexact([-1] + [0] * (3 * j - 1) + [1], [1, 1, 1])
        c1 = congruent_to_I(rho(n, power(S12, j)), g1)
        c2 = congruent_to_I(rho(n, power(T3, j)), g2)
        print("   j =", j, ": sigma_1^{2j} = I mod (t^{2j}-1)/(t+1):", c1,
              "; Delta_3^{2j} = I mod (t^{3j}-1)/(t^2+t+1):", c2)
        ok &= c1 and c2
    # sharpness: sigma_1^{2j} is NOT = I mod Phi_2, Delta_3^{2j} NOT = I mod Phi_3
    s1 = not congruent_to_I(rho(n, power(S12, 3)), cyclotomic(2))
    s2 = not congruent_to_I(rho(n, power(T3, 3)), cyclotomic(3))
    print("   sharpness: sigma_1^6 != I mod Phi_2:", s1, "; Delta_3^6 != I mod Phi_3:", s2)
    ok &= s1 and s2

    b = comm(A(1, 4), comm(A(2, 4), A(3, 4)))
    ok_b = brunnian_control(n, b)
    print("3. b = [A14,[A24,A34]] Brunnian and nontrivial:", ok_b); ok &= ok_b
    # sign-coherent case: Brunnian b (in gamma_2 P_4) has rho = I mod (t-1)^2
    sc = congruent_to_I(rho(n, b), [1, -2, 1]) and not is_ident(rho(n, b))
    print("   rho_4(b) = I mod (t-1)^2 and != I:", sc); ok &= sc

    # 4. Psi_q = [X_q, b] for q = 2..24
    for q in range(2, 25):
        X = twist_for(q)
        Psi = comm(X, b)
        R = rho(n, Psi)
        cong = congruent_to_I(R, plist_mul([1, -2, 1], cyclotomic(q)))
        nonid = not is_ident(R)
        pure = rho_at_one_is_I(R)
        print("4. q =", q, ": len", len(Psi), "; rho_4(Psi_q) = I mod (t-1)^2 Phi_q:", cong,
              "; != I:", nonid, "; pure:", pure)
        ok &= cong and nonid and pure

    # 5. jets: iterated commutators, rho = I mod product of the factor ideals
    jets = [("(t+1)^2", [2, 2]), ("Phi_4^2 Phi_3", [4, 4, 3]), ("(t-1) Phi_2^2 Phi_8", [1, 2, 2, 8])]
    for name, qs in jets:
        w = b
        g = [1]
        for q in qs:
            X = S12 if q == 1 else twist_for(q)   # q = 1: any pure braid will do
            w = comm(X, w)
            g = plist_mul(g, cyclotomic(q))
        g = plist_mul(g, [1, -2, 1])  # the extra (t-1)^2 factor from b in [P_4,P_4]
        R = rho(n, w)
        cong = congruent_to_I(R, g)
        nonid = not is_ident(R)
        print("5. jet", name, "x (t-1)^2: len", len(w), "; = I mod g:", cong, "; != I:", nonid)
        ok &= cong and nonid

    # 6. calibration n = 3: Brun_3 meets ker rho_3 mod Phi_q for q >= 3, not via 3-point twists
    n3 = 3
    b3 = comm(A(1, 3), A(2, 3))
    c6 = brunnian_control(n3, b3)
    for q in (3, 4, 8):
        Psi3 = comm(twist_for(q), b3)
        R3 = rho(n3, Psi3)
        c6 &= congruent_to_I(R3, plist_mul([1, -2, 1], cyclotomic(q))) and not is_ident(R3)
    print("6. n = 3: [A_12^j, [A13,A23]] = I mod (t-1)^2 Phi_q for q = 3,4,8, != I (b3 Brunnian by control, Psi Brunnian by normality):", c6)
    ok &= c6
    # the 3-point twist is central in B_3, so its commutators die (so this mechanism gives nothing at t = -1 in B_3)
    c6b = is_ident(rho(n3, comm(power(T3, 2), b3)))
    print("   n = 3: [Delta_3^4, b3] has identity Burau (central twist):", c6b)
    ok &= c6b

    D3 = minus_ident(rho(3, T3))
    print("7. rho_3((s1 s2)^3) - I, entries as Laurent dicts:", D3)
    print("ALL CHECKS PASS:", ok)
    return 0 if ok else 1

if __name__ == "__main__":
    sys.exit(main())
