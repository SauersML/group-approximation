"""Sanity checks for the char-p Burger lamp reduction (swarm-0917-w17 nv-break).

Checks, on finite windows, the formulas used in
research/char-p-burger-lamp-realizations-refute-haagerup-proof.md and
research/injective-char-p-lamp-realizations-miss-fixed-points-proof.md:

 1. adjoint: <A m, chi> = <m, A^T(sigma) chi>, with (sigma chi)_k = chi_(k+1);
 2. gamma . chi := (gamma^-1)^T(sigma) chi is a left action;
 3. matrix identities: h e12(r) h^-1 = e12(t^2 r), h e21(r) h^-1 = e21(t^-2 r),
    w(t) w(1)^-1 = h;
 4. affine unipotent xi -> u xi + v has order 4 for p = 2 when v_1 != 0, order p for p odd;
 5. affine torus xi -> D xi + v (D dual of diag(c, c^-1)) has order p - 1 and one fixed point;
 6. baker map B on C^2 is the left shift in the coordinates Theta, and
    phi o B^k = (sigma^-1 x sigma) o phi for the block code used in Proposition B.

Pure Python; no randomness beyond a fixed seed.
"""
import random

random.seed(20260919)


# ---------- Laurent polynomials over F_p: dict exponent -> coefficient ----------
def padd(a, b, p):
    c = dict(a)
    for k, v in b.items():
        c[k] = (c.get(k, 0) + v) % p
    return {k: v for k, v in c.items() if v}


def pmul(a, b, p):
    c = {}
    for i, x in a.items():
        for j, y in b.items():
            c[i + j] = (c.get(i + j, 0) + x * y) % p
    return {k: v for k, v in c.items() if v}


def pneg(a, p):
    return {k: (-v) % p for k, v in a.items() if v % p}


def mat_mul(A, B, p):
    return [[padd(pmul(A[i][0], B[0][j], p), pmul(A[i][1], B[1][j], p), p) for j in range(2)] for i in range(2)]


def e12(r):
    return [[{0: 1}, r], [{}, {0: 1}]]


def e21(r):
    return [[{0: 1}, {}], [r, {0: 1}]]


def diag(a, b):
    return [[a, {}], [{}, b]]


def inv_el(A, p):
    # inverse of a determinant-one 2x2 matrix: [[d, -b], [-c, a]]
    return [[A[1][1], pneg(A[0][1], p)], [pneg(A[1][0], p), A[0][0]]]


def rand_poly(p, lo=-2, hi=2):
    return {k: v for k, v in ((k, random.randrange(p)) for k in range(lo, hi + 1)) if v}


# ---------- configurations: dict position -> value, on a window ----------
W = 40  # window half-width for chi


def act_poly_on_seq(r, chi, p):
    """r(sigma) chi, (sigma chi)_k = chi_(k+1); computed where defined inside the window."""
    out = {}
    for k in range(-W + 5, W - 5):
        s = 0
        for j, c in r.items():
            s += c * chi.get(k + j, 0)
        out[k] = s % p
    return out


def act_mat_T(A, xi, p):
    """A^T(sigma) applied to xi = (alpha, beta)."""
    al, be = xi
    # (A^T xi)_j = sum_i A_ij(sigma) xi_i
    res = []
    for j in range(2):
        s = {}
        for i in range(2):
            t = act_poly_on_seq(A[i][j], (al, be)[i], p)
            for k, v in t.items():
                s[k] = (s.get(k, 0) + v) % p
        res.append(s)
    return tuple(res)


def pair(m, xi, p):
    a, b = m
    al, be = xi
    return (sum(v * al.get(k, 0) for k, v in a.items()) + sum(v * be.get(k, 0) for k, v in b.items())) % p


def mat_vec(A, m, p):
    return (padd(pmul(A[0][0], m[0], p), pmul(A[0][1], m[1], p), p),
            padd(pmul(A[1][0], m[0], p), pmul(A[1][1], m[1], p), p))


def rand_seq(p):
    return {k: random.randrange(p) for k in range(-W, W + 1)}


def check_adjoint(p, trials=200):
    for _ in range(trials):
        A = [[rand_poly(p), rand_poly(p)], [rand_poly(p), rand_poly(p)]]
        m = (rand_poly(p, -5, 5), rand_poly(p, -5, 5))
        xi = (rand_seq(p), rand_seq(p))
        lhs = pair(mat_vec(A, m, p), xi, p)
        rhs = pair(m, act_mat_T(A, xi, p), p)
        assert lhs == rhs, (p, A, m)
    return True


def dual_act(g, xi, p):
    return act_mat_T(inv_el(g, p), xi, p)


def check_left_action(p, trials=50):
    for _ in range(trials):
        g1 = mat_mul(e12(rand_poly(p, -1, 1)), e21(rand_poly(p, -1, 1)), p)
        g2 = mat_mul(e21(rand_poly(p, -1, 1)), e12(rand_poly(p, -1, 1)), p)
        m = (rand_poly(p, -3, 3), rand_poly(p, -3, 3))
        xi = (rand_seq(p), rand_seq(p))
        # (g.chi)(m) = chi(g^-1 m); compare (g1 g2).chi and g1.(g2.chi) through the pairing
        g12 = mat_mul(g1, g2, p)
        lhs = pair(mat_vec(inv_el(g12, p), m, p), xi, p)
        rhs = pair(mat_vec(inv_el(g1, p), m, p), dual_act(g2, xi, p), p)
        assert lhs == rhs
    return True


def eqmat(A, B):
    return all(A[i][j] == B[i][j] for i in range(2) for j in range(2))


def check_identities(p):
    t, ti = {1: 1}, {-1: 1}
    h = diag(t, ti)
    hi = diag(ti, t)
    for _ in range(30):
        r = rand_poly(p, -3, 3)
        assert eqmat(mat_mul(mat_mul(h, e12(r), p), hi, p), e12(pmul({2: 1}, r, p)))
        assert eqmat(mat_mul(mat_mul(h, e21(r), p), hi, p), e21(pmul({-2: 1}, r, p)))

    def w(u, uinv):
        return mat_mul(mat_mul(e12(u), e21(pneg(uinv, p)), p), e12(u), p)
    w1 = w({0: 1}, {0: 1})
    assert eqmat(mat_mul(w(t, ti), inv_el(w1, p), p), h)
    return True


# ---------- affine maps on finite truncations (radius-0, so windows are exact) ----------
def affine_order(p, lin, v, n=6, maxord=50):
    """lin: function on pairs of tuples; v: pair of tuples. Return order of xi -> lin(xi)+v on all of (F_p^2)^n."""
    import itertools
    pts = list(itertools.product(range(p), repeat=2 * n))
    def f(x):
        al, be = x[:n], x[n:]
        a2, b2 = lin(al, be)
        return tuple((a2[i] + v[0][i]) % p for i in range(n)) + tuple((b2[i] + v[1][i]) % p for i in range(n))
    for k in range(1, maxord + 1):
        ok = True
        for x in pts[:: max(1, len(pts) // 400)]:
            y = x
            for _ in range(k):
                y = f(y)
            if y != x:
                ok = False
                break
        if ok:
            return k, [x for x in pts if f(x) == x]
    return None, None


def check_affine_unipotent():
    res = {}
    for p in (2, 3, 5):
        n = 3 if p == 5 else 4
        lin = lambda al, be, p=p: (al, tuple((be[i] - al[i]) % p for i in range(len(al))))
        v = (tuple([1] + [0] * (n - 1)), tuple([0] * n))
        k, _ = affine_order(p, lin, v, n=n)
        res[p] = k
    assert res[2] == 4 and res[3] == 3 and res[5] == 5, res
    return res


def check_affine_torus():
    res = {}
    for p, c in ((3, 2), (5, 2), (7, 3)):
        cinv = pow(c, p - 2, p)
        n = 2
        lin = lambda al, be, p=p, c=c, cinv=cinv: (tuple(cinv * a % p for a in al), tuple(c * b % p for b in be))
        v = (tuple(random.randrange(p) for _ in range(n)), tuple(random.randrange(p) for _ in range(n)))
        k, fixed = affine_order(p, lin, v, n=n)
        res[p] = (k, len(fixed))
        assert k == p - 1 and len(fixed) == 1, (p, k, len(fixed))
    return res


# ---------- baker map and the block code of Proposition B ----------
def check_baker(p=3, k=4, N=60, trials=100):
    # points of C^2 truncated: x, y lists of length N
    import itertools
    assert 2 ** k >= p * p
    tau_table = list(itertools.product(range(p), repeat=2))
    def tau(bits):
        idx = int("".join(map(str, bits)), 2)
        return tau_table[idx % (p * p)] if idx < 2 ** k else None
    def Theta(x, y):
        z = {}
        for j in range(len(x)):
            z[j] = x[j]
        for j in range(len(y)):
            z[-j - 1] = y[j]
        return z
    def B(x, y):
        return x[1:], [x[0]] + y
    def phi(x, y, J):
        z = Theta(x, y)
        al, be = {}, {}
        for j in range(-J, J + 1):
            a, b = tau([z[j * k + i] for i in range(k)])
            al[-j] = a      # psi reverses the alpha index
            be[j] = b
        return al, be
    for _ in range(trials):
        x = [random.randrange(2) for _ in range(N)]
        y = [random.randrange(2) for _ in range(N)]
        # Theta B Theta^-1 = left shift
        zx, zy = B(x, y)
        z0, z1 = Theta(x, y), Theta(zx, zy)
        for j in range(-N + 2, N - 2):
            assert z1[j] == z0[j + 1]
        # phi o B^k = (sigma^-1 x sigma) o phi on a window
        xx, yy = x, y
        for _ in range(k):
            xx, yy = B(xx, yy)
        J = 5
        al0, be0 = phi(x, y, J + 1)
        al1, be1 = phi(xx, yy, J)
        for j in range(-J, J + 1):
            # (sigma^-1 alpha)_j = alpha_(j-1),  (sigma beta)_j = beta_(j+1)
            assert al1[j] == al0[j - 1], ("alpha", j)
            assert be1[j] == be0[j + 1], ("beta", j)
    return True


if __name__ == "__main__":
    for p in (2, 3, 5):
        print("p=%d adjoint:" % p, check_adjoint(p), " left action:", check_left_action(p),
              " identities:", check_identities(p))
    print("affine unipotent orders (v_1 != 0):", check_affine_unipotent())
    print("affine torus (order, #fixed points):", check_affine_torus())
    print("baker conjugacy and block-code factor (p=3, k=4):", check_baker())
    print("baker conjugacy and block-code factor (p=2, k=2):", check_baker(p=2, k=2))
    print("ALL CHECKS PASSED")
