#!/usr/bin/env python3
"""Exact closed-walk counts for Thompson's group F and a certified lower bound on
the spectral radius of simple random walk for the generators {x0^{+-1}, x1^{+-1}}.

Elements of F are PL homeomorphisms of [0,1] with dyadic breakpoints and slopes
powers of 2. A map is stored exactly by its minimal breakpoint lists (xs, ys),
coordinates as integers over 2^K. Every division is checked to be exact, so an
insufficient K fails loudly instead of rounding.

Output: JSON with c_{2j} = #{words of length 2j that are trivial in F} for j <= N,
consistency checks, and a rational certificate theta with rho(F)^2 > theta.

Certificate logic (all exact rational arithmetic):
  mu = spectral measure of P^2 at delta_e, P = (x0 + x0^-1 + x1 + x1^-1)/4,
  moments M_j = c_{2j} / 16^j. Monic orthogonal polynomials p_0..p_k are built by
  the three-term recurrence from M_0..M_{2k-1}; <p_j,p_j> > 0 is verified for j < k.
  If p_k(theta) < 0 for a rational theta, then the largest zero x_k of p_k exceeds
  theta, and x_k <= sup supp mu <= ||P||^2 (orthogonality argument in the proof node).
"""
import bisect, itertools, json, math, sys, time
from fractions import Fraction

K = 64
ONE = 1 << K


def dy(p, q):
    """p/q with q a power of 2, scaled by 2^K."""
    assert q & (q - 1) == 0 and (p * ONE) % q == 0
    return p * ONE // q


def make(points):
    xs = tuple(dy(*a) for a, _ in points)
    ys = tuple(dy(*b) for _, b in points)
    return canon(list(zip(xs, ys)))


def canon(pts):
    out = [pts[0]]
    for i in range(1, len(pts) - 1):
        x0, y0 = out[-1]
        x1, y1 = pts[i]
        x2, y2 = pts[i + 1]
        if (y1 - y0) * (x2 - x1) != (y2 - y1) * (x1 - x0):
            out.append((x1, y1))
    out.append(pts[-1])
    return (tuple(p[0] for p in out), tuple(p[1] for p in out))


def ev(f, x):
    xs, ys = f
    i = bisect.bisect_right(xs, x) - 1
    if i >= len(xs) - 1:
        assert x == ONE
        return ONE
    num = (x - xs[i]) * (ys[i + 1] - ys[i])
    q, r = divmod(num, xs[i + 1] - xs[i])
    if r:
        raise ArithmeticError("dyadic depth exceeds K")
    return ys[i] + q


def inv(f):
    return (f[1], f[0])


def comp(f, g):
    """f o g : apply g first."""
    gi = inv(g)
    cand = set(g[0])
    for x in f[0]:
        cand.add(ev(gi, x))
    xs = sorted(cand)
    return canon([(x, ev(f, ev(g, x))) for x in xs])


IDENT = make([((0, 1), (0, 1)), ((1, 1), (1, 1))])
X0 = make([((0, 1), (0, 1)), ((1, 2), (1, 4)), ((3, 4), (1, 2)), ((1, 1), (1, 1))])
X1 = make([((0, 1), (0, 1)), ((1, 2), (1, 2)), ((3, 4), (5, 8)), ((7, 8), (3, 4)),
           ((1, 1), (1, 1))])
GENS = [X0, inv(X0), X1, inv(X1)]


def word_eval(letters):
    g = IDENT
    for s in letters:
        g = comp(g, GENS[s])
    return g


def relation_checks():
    a, A, b, B = 0, 1, 2, 3
    # [x0 x1^-1, x0^-1 x1 x0] and [x0 x1^-1, x0^-2 x1 x0^2] as words
    def commutator(u, v):
        inv_letter = {0: 1, 1: 0, 2: 3, 3: 2}
        ui = [inv_letter[s] for s in reversed(u)]
        vi = [inv_letter[s] for s in reversed(v)]
        return ui + vi + u + v
    u = [a, B]
    r1 = commutator(u, [A, b, a])
    r2 = commutator(u, [A, A, b, a, a])
    return {
        "r1_trivial": word_eval(r1) == IDENT,
        "r2_trivial": word_eval(r2) == IDENT,
        "x0_x1_noncommuting": comp(X0, X1) != comp(X1, X0),
        "relator_lengths": [len(r1), len(r2)],
    }


def brute_counts(max_len):
    counts = {}
    for L in range(2, max_len + 1, 2):
        c = 0
        for w in itertools.product(range(4), repeat=L):
            if word_eval(w) == IDENT:
                c += 1
        counts[L] = c
    return counts


def dp_counts(N, log):
    cur = {IDENT: 1}
    c2 = [1]
    sizes = [1]
    for j in range(1, N + 1):
        nxt = {}
        get = nxt.get
        for g, m in cur.items():
            for s in GENS:
                h = comp(g, s)
                nxt[h] = get(h, 0) + m
        cur = nxt
        c2.append(sum(m * m for m in cur.values()))
        sizes.append(len(cur))
        log(f"depth {j}: support {len(cur)}, c_{2*j} = {c2[-1]}")
    return c2, sizes


def poly_mul_x(p):
    return [Fraction(0)] + p


def poly_add(p, q, a=1, b=1):
    n = max(len(p), len(q))
    p = p + [Fraction(0)] * (n - len(p))
    q = q + [Fraction(0)] * (n - len(q))
    return [a * x + b * y for x, y in zip(p, q)]


def inner(p, q, M):
    return sum(pi * qj * M[i + j] for i, pi in enumerate(p) for j, qj in enumerate(q)
               if pi and qj)


def poly_eval(p, x):
    r = Fraction(0)
    for c in reversed(p):
        r = r * x + c
    return r


def certificate(c2):
    N = len(c2) - 1
    M = [Fraction(c, 16 ** j) for j, c in enumerate(c2)]
    k = (N + 1) // 2
    p_prev, p = [Fraction(0)], [Fraction(1)]
    norms = []
    for j in range(k):
        nj = inner(p, p, M)
        norms.append(nj)
        assert nj > 0, "Hankel matrix not positive definite"
        alpha = inner(poly_mul_x(p), p, M) / nj
        beta = nj / norms[j - 1] if j > 0 else Fraction(0)
        p_next = poly_add(poly_add(poly_mul_x(p), p, 1, -alpha), p_prev, 1, -beta)
        p_prev, p = p, p_next
    pk = p
    lo, hi = Fraction(0), Fraction(1)
    assert poly_eval(pk, hi) > 0
    # largest zero lies in (0, 1): bisect on the sign pattern from the top
    grid = [Fraction(i, 4096) for i in range(4096, -1, -1)]
    start = next(t for t in grid if poly_eval(pk, t) < 0)
    lo, hi = start, start + Fraction(1, 4096)
    for _ in range(60):
        mid = (lo + hi) / 2
        if poly_eval(pk, mid) < 0:
            lo = mid
        else:
            hi = mid
    theta = Fraction(math.floor(lo * 10 ** 9), 10 ** 9)
    assert poly_eval(pk, theta) < 0 or pk_has_root_above(pk, theta)
    r = Fraction(math.isqrt(math.floor(theta * 10 ** 12)), 10 ** 6)
    assert r * r <= theta
    ratios = [float(M[j + 1] / M[j]) for j in range(N)]
    return {
        "k": k,
        "theta": f"{theta.numerator}/{theta.denominator}",
        "p_k_at_theta_negative": poly_eval(pk, theta) < 0,
        "rho_lower_bound": f"{r.numerator}/{r.denominator}",
        "rho_lower_bound_float": float(r),
        "ratio_bound_sqrt_M_N_over_M_Nm1": math.sqrt(ratios[-1]),
        "root_bound_M_N_pow": float(M[N]) ** (1 / (2 * N)),
        "log_convex": all(M[j] * M[j] <= M[j - 1] * M[j + 1] for j in range(1, N)),
    }


def pk_has_root_above(pk, theta):
    return False


def main():
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 10
    out = {"N": N, "K": K}
    log = lambda s: print(s, file=sys.stderr, flush=True)
    t0 = time.time()
    out["relations"] = relation_checks()
    log(f"relations {out['relations']}")
    brute = brute_counts(8)
    out["brute_force_counts"] = brute
    c2, sizes = dp_counts(N, log)
    out["c2"] = c2
    out["support_sizes"] = sizes
    out["brute_matches_dp"] = all(brute[L] == c2[L // 2] for L in brute)
    out["z2_upper_bound_ok"] = all(c <= math.comb(2 * j, j) ** 2 for j, c in enumerate(c2))
    out["certificate"] = certificate(c2)
    out["seconds"] = round(time.time() - t0, 1)
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
