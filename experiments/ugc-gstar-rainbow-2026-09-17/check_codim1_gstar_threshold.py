"""Checks for research/codim-one-gstar-threshold-is-two-to-minus-half-l.md.

GStar_n (list-star-coherent-selector-witnesses-put-np-in-rp, lines 271-276):
F gives a functional F(S) on every subspace S of F_2^n of dimension l-1 or l.
W uniform (l-1)-space, u uniform in F_2^n.
  val(F) = Pr[u notin W, F(W+u)|_W = F(W)]
  D(F)   = E_W min_psi Pr_u[u notin W, sat, F(W+u)(u) != psi(u)]   (psi over ALL
           functionals of F_2^n, the best possible list).
A violator at gamma is an F with val >= 1/2 + gamma and D >= gamma: then
GStar_n(gamma, gamma') fails for every gamma' > 0 and every list size.

Parts
  A  primal brute force of val and D at (n,l) = (3,2), (4,3) against the rainbow
     graph dictionary (val = sum_W s(W)/(4N), D = #sat triangle lines/(4N)).
  B  triangle bound: exhaustive at d = 3, annealing at d = 4..7, and the
     identities Pi = 3 f + t, sum s = N + 2 f + t.
  C  Sidon (APN graph) violators for d = 4..20, exact counts by a Walsh-Hadamard
     autocorrelation, checked against brute force for d <= 9; comparison with
     2^(1-l) and with the spectral cap delta(l).
  D  the K4 example at d = 3 (gamma = 1/7).
  E  the lift to n > l+1: primal brute force at (n,l) = (4,2), (5,2), (5,3), (6,3).
Exits 0 iff every check passes.
"""
import itertools
import math
import random
import sys
from fractions import Fraction as Fr

import numpy as np

FAIL = []


def check(cond, msg):
    if not cond:
        FAIL.append(msg)
        print("FAIL:", msg)


def dot(a, b):
    return bin(a & b).count("1") & 1


def span(vecs):
    s = {0}
    for v in vecs:
        s |= {x ^ v for x in s}
    return frozenset(s)


def subspaces(n, k):
    """All k-dimensional subspaces of F_2^n, as frozensets."""
    out = set()
    for vecs in itertools.combinations(range(1, 1 << n), k):
        s = span(vecs)
        if len(s) == 1 << k:
            out.add(s)
    return sorted(out, key=lambda s: sorted(s))


def perp(n, S):
    return frozenset(x for x in range(1 << n) if all(dot(x, s) == 0 for s in S))


# ---------------------------------------------------------------- primal model
def primal_val_D(n, l, xS, xW, Ws):
    """Exact val and D of the primal GStar_n quantities.

    xS[S], xW[W] are vectors of F_2^n; the functional is u -> <x, u>.
    """
    tot_val = Fr(0)
    tot_D = Fr(0)
    U = 1 << n
    for W in Ws:
        sat_u = []
        for u in range(U):
            if u in W:
                continue
            S = frozenset(W | {w ^ u for w in W})
            if all(dot(xS[S] ^ xW[W], w) == 0 for w in W):
                sat_u.append((u, dot(xS[S], u)))
        tot_val += Fr(len(sat_u), U)
        best = min(sum(1 for (u, b) in sat_u if dot(psi, u) != b)
                   for psi in range(U))
        tot_D += Fr(best, U)
    return tot_val / len(Ws), tot_D / len(Ws)


# ----------------------------------------------------------- rainbow graphs
def lines_of(d):
    """All 2-dim subspaces of F_2^d as sorted triples of nonzero vectors."""
    L = set()
    for a in range(1, 1 << d):
        for b in range(a + 1, 1 << d):
            L.add(tuple(sorted((a, b, a ^ b))))
    return sorted(L)


def line_type(edge, P):
    """Type of the line P for the rainbow graph edge[colour] = (x, x^colour)."""
    es = [frozenset(edge[c]) for c in P]
    adj = [bool(es[i] & es[j]) for (i, j) in ((0, 1), (0, 2), (1, 2))]
    k = sum(adj)
    if k == 3:
        return "FT" if not (es[0] & es[1] & es[2]) else "FU"
    if k == 1:
        return "t"
    check(k == 0, "adjacency must be 0, 1 or 3 (transitivity)")
    return "s1"


def coset_key(x, P):
    return min(x, x ^ P[0], x ^ P[1], x ^ P[2])


def best_cosets(d, edge, lines):
    """For each line the coset maximising s; for full lines the common coset."""
    out = {}
    for P in lines:
        cnt = {}
        for c in P:
            k = coset_key(edge[c][0], P)
            cnt[k] = cnt.get(k, 0) + 1
        out[P] = max(cnt, key=lambda k: (cnt[k], -k))
    return out


def graph_val_D(d, edge, choice, lines):
    """Literal val and D from the dictionary, given F(W) = coset choice[P]."""
    N = len(lines)
    ssum = 0
    ft = 0
    for P in lines:
        s = sum(1 for c in P if coset_key(edge[c][0], P) == choice[P])
        ssum += s
        if s == 3 and line_type(edge, P) == "FT":
            ft += 1
    return Fr(ssum, 4 * N), Fr(ft, 4 * N)


def part_A():
    print("Part A: primal brute force vs rainbow dictionary (codim 1)")
    rng = random.Random(1)
    for d in (3, 4):
        n, l = d, d - 1
        Ss = subspaces(n, l)
        Ws = subspaces(n, l - 1)
        lines = lines_of(d)
        nu_of = {S: max(perp(n, S)) for S in Ss}
        S_of = {nu: S for S, nu in nu_of.items()}
        P_of = {W: tuple(sorted(perp(n, W) - {0})) for W in Ws}
        check(sorted(P_of.values()) == lines, "W <-> lines bijection")
        trials = 0
        for trial in range(120 if d == 3 else 40):
            mode = trial % 3
            if mode == 2:
                # a Sidon-type table: K4 on {0,e1,e2,e3} plus a random rest
                edge = {c: (rng.randrange(1 << d),) for c in range(1, 1 << d)}
                for a, b in itertools.combinations((0, 1, 2, 4), 2):
                    edge[a ^ b] = (a,)
            else:
                edge = {c: (rng.randrange(1 << d),) for c in range(1, 1 << d)}
            edge = {c: (v[0], v[0] ^ c) for c, v in edge.items()}
            if mode == 0:
                choice = {P: coset_key(rng.randrange(1 << d), P) for P in lines}
            else:
                choice = best_cosets(d, edge, lines)
            xS = {S_of[c]: edge[c][0] for c in edge}
            xW = {W: choice[P_of[W]] for W in Ws}
            pv, pD = primal_val_D(n, l, xS, xW, Ws)
            gv, gD = graph_val_D(d, edge, choice, lines)
            check(pv == gv, "val mismatch d=%d" % d)
            check(pD == gD, "D mismatch d=%d" % d)
            trials += 1
        print("  d=%d: %d random tables, primal == dictionary for val and D"
              % (d, trials))


# --------------------------------------------------------- triangle bound
def tri_cap(d):
    m = (1 << d) - 1
    return math.sqrt(2) / 3 * m ** 1.5


def delta_cap(l):
    """Spectral cap on D_lit at n = l+1: (sqrt2/2) (2^(l+1)-1)^(1/2)/(2^(l+1)-2)."""
    d = l + 1
    return math.sqrt(2) / 2 * math.sqrt((1 << d) - 1) / ((1 << d) - 2)


def type_counts(d, edge, lines):
    cnt = {"FT": 0, "FU": 0, "t": 0, "s1": 0}
    for P in lines:
        cnt[line_type(edge, P)] += 1
    return cnt


def adjacent_pairs(d, edge):
    deg = [0] * (1 << d)
    for (x, y) in edge.values():
        deg[x] += 1
        deg[y] += 1
    return sum(k * (k - 1) // 2 for k in deg)


def tri_through(d, edge, c):
    x, y = edge[c]
    k = 0
    for z in range(1 << d):
        if z in (x, y):
            continue
        if set(edge[x ^ z]) == {x, z} and set(edge[y ^ z]) == {y, z}:
            k += 1
    return k


def part_B():
    print("Part B: triangle bound #FT <= (sqrt2/3) m^(3/2)")
    d = 3
    lines = lines_of(d)
    N = len(lines)
    cols = list(range(1, 8))
    best = 0
    for xs in itertools.product(range(4), repeat=7):
        edge = {}
        for c, j in zip(cols, xs):
            reps = sorted(min(x, x ^ c) for x in range(8))
            reps = sorted(set(reps))
            x = reps[j]
            edge[c] = (x, x ^ c)
        cnt = type_counts(d, edge, lines)
        f = cnt["FT"] + cnt["FU"]
        check(adjacent_pairs(d, edge) == 3 * f + cnt["t"], "Pi identity d=3")
        best = max(best, cnt["FT"])
    check(best <= tri_cap(d), "triangle cap d=3")
    print("  d=3 exhaustive (16384 graphs): max #FT = %d, cap %.3f, max D_lit"
          " = %s, delta(2) = %.4f" % (best, tri_cap(d), Fr(best, 4 * N),
                                      delta_cap(2)))
    check(Fr(best, 4 * N) <= delta_cap(2), "delta cap d=3")
    rng = random.Random(7)
    for d in (4, 5, 6, 7):
        lines = lines_of(d) if d <= 6 else None
        cols = list(range(1, 1 << d))
        edge = {}
        for c in cols:
            x = rng.randrange(1 << d)
            edge[c] = (x, x ^ c)
        T = sum(tri_through(d, edge, c) for c in cols) // 3
        bestT = T
        temp = 1.0
        iters = {4: 20000, 5: 20000, 6: 12000, 7: 6000}[d]
        for it in range(iters):
            c = rng.choice(cols)
            old = edge[c]
            before = tri_through(d, edge, c)
            x = rng.randrange(1 << d)
            edge[c] = (x, x ^ c)
            after = tri_through(d, edge, c)
            if after >= before or rng.random() < math.exp((after - before) / temp):
                T += after - before
                bestT = max(bestT, T)
            else:
                edge[c] = old
            temp = max(0.02, temp * 0.9995)
        if lines is not None:
            cnt = type_counts(d, edge, lines)
            check(cnt["FT"] == T, "incremental triangle count d=%d" % d)
            f = cnt["FT"] + cnt["FU"]
            check(adjacent_pairs(d, edge) == 3 * f + cnt["t"],
                  "Pi identity d=%d" % d)
        N = ((1 << d) - 1) * ((1 << d) - 2) // 6
        check(bestT <= tri_cap(d), "triangle cap d=%d" % d)
        check(bestT / (4 * N) <= delta_cap(d - 1), "delta cap d=%d" % d)
        print("  d=%d annealed: max #FT = %d, cap %.1f; D_lit %.5f <= delta(%d)"
              " = %.5f" % (d, bestT, tri_cap(d), bestT / (4 * N), d - 1,
                           delta_cap(d - 1)))


# ------------------------------------------------------- Sidon violators
IRRED = {1: 0b11, 2: 0b111, 3: 0b1011, 4: 0b10011, 5: 0b100101,
         6: 0b1000011, 7: 0b10000011, 8: 0b100011011, 9: 0b1000010001,
         10: 0b10000001001}


def gf_mul(a, b, h):
    r = 0
    while b:
        if b & 1:
            r ^= a
        b >>= 1
        a <<= 1
        if a >> h:
            a ^= IRRED[h]
    return r


def apn_set(h):
    """{(x, x^3)} in F_2^(2h), x = 0 first; Sidon by x^3+y^3 = a(a^2+xy)."""
    return [x | (gf_mul(x, gf_mul(x, x, h), h) << h) for x in range(1 << h)]


def is_sidon(S):
    seen = set()
    for a, b in itertools.combinations(S, 2):
        if a ^ b in seen:
            return False
        seen.add(a ^ b)
    return True


def C2(x):
    return x * (x - 1) // 2


def C3(x):
    return x * (x - 1) * (x - 2) // 6


def wht(v):
    v = v.copy()
    h = 1
    n = len(v)
    while h < n:
        v = v.reshape(-1, 2, h)
        a = v[:, 0, :].copy()
        b = v[:, 1, :].copy()
        v[:, 0, :] = a + b
        v[:, 1, :] = a - b
        v = v.reshape(n)
        h *= 2
    return v


def sidon_counts(d, Sp):
    """Exact FT, FU, t, s1 of G = K_{S'} + star at 0, by autocorrelation."""
    sig = len(Sp)
    A = [a for a in Sp if a]
    SA = [a ^ b for a, b in itertools.combinations(A, 2)]
    D = 1 << d
    Y = np.zeros(D, dtype=np.int64)
    Y[0] = 1
    Y[SA] = 1
    check(int(Y.sum()) == 1 + C2(sig - 1), "Sigma(A) distinct and nonzero")
    check(not any(Y[a] for a in A), "Sigma(A) disjoint from A")
    M = D - int(Y.sum())
    hat = wht(Y)
    corr = wht(hat * hat) // D          # corr[s] = #{y in Y : y^s in Y}
    ny = int(Y.sum())
    X2 = len(SA) * (D - 2 * ny) + int(corr[np.array(SA, dtype=np.int64)].sum())
    check(X2 % 2 == 0, "X parity")
    X = X2 // 2
    N = C2(D - 1) // 3
    FT = C3(sig)
    check((C2(M) - X) % 3 == 0, "FU integrality")
    FU = (C2(M) - X) // 3
    t = X - C2(sig - 1)
    s1 = N - FT - FU - t
    return dict(FT=FT, FU=FU, t=t, s1=s1, N=N, M=M)


def gamma_star(c):
    N = c["N"]
    ssum = 3 * (c["FT"] + c["FU"]) + 2 * c["t"] + c["s1"]
    gval = Fr(ssum - 2 * N, 4 * N)
    D0 = Fr(c["FT"], 4 * N)
    return min(gval, D0), gval, D0


def sidon_graph(d, Sp):
    edge = {}
    for a, b in itertools.combinations(Sp, 2):
        check(a ^ b not in edge, "rainbow K_S'")
        edge[a ^ b] = (a, b)
    for z in range(1, 1 << d):
        if z not in edge:
            edge[z] = (0, z)
    return edge


def thm_sigma(l):
    return math.isqrt(1 << l)          # floor(2^(l/2))


def thm_gamma(l):
    """(gamma_thm, condition) for sigma = floor(2^(l/2)) at d = l+1."""
    d = l + 1
    m = (1 << d) - 1
    sig = thm_sigma(l)
    M = m - C2(sig - 1)
    cond = 2 * C2(M) - C2(m) >= 3 * C3(sig)
    return Fr(3 * C3(sig), 4 * C2(m)), cond


def part_C(dmax):
    print("Part C: Sidon (APN graph) violators, literal normalisation")
    print("   d  l  sigma*  gamma*        gamma*2^(l/2)  2^(1-l)      "
          "delta(l)   gamma*/2^(1-l)  gamma_thm*2^(l/2)")
    first_beat = None
    for d in range(4, dmax + 1):
        l = d - 1
        h = d // 2
        G = apn_set(h)
        check(is_sidon(G), "APN graph Sidon h=%d" % h)
        top = 1 << h
        if d <= 10:
            sigmas = range(3, top + 1)
        else:
            sigmas = sorted(set(max(3, min(top, int(round(c * 2 ** (d / 2)))))
                                for c in [0.40 + 0.02 * i for i in range(31)]))
        best = None
        for sig in sigmas:
            c = sidon_counts(d, G[:sig])
            g, gval, D0 = gamma_star(c)
            if best is None or g > best[0]:
                best = (g, sig)
            if d <= 7 or (d <= 9 and sig in (top // 2, top)):
                edge = sidon_graph(d, G[:sig])
                lines = lines_of(d)
                tc = type_counts(d, edge, lines)
                check(all(tc[k] == c[k] for k in tc), "counts d=%d sig=%d"
                      % (d, sig))
                v, Dg = graph_val_D(d, edge, best_cosets(d, edge, lines), lines)
                check(v == Fr(1, 2) + gval and Dg == D0,
                      "val/D formula d=%d sig=%d" % (d, sig))
        g, sig = best
        check(float(g) <= delta_cap(l) + 1e-12, "violator below cap d=%d" % d)
        sthm = thm_sigma(l)
        check(sthm <= top, "theorem sigma fits the APN graph d=%d" % d)
        gthm, cond = thm_gamma(l)
        if d >= 5:
            check(cond, "theorem inequality d=%d" % d)
            gt, _, _ = gamma_star(sidon_counts(d, G[:sthm]))
            check(gt >= gthm, "exact gamma >= gamma_thm d=%d" % d)
        if g > Fr(2, 1 << l) and first_beat is None:
            first_beat = l
        print("  %2d %2d %6d  %.6e  %.4f         %.6e  %.4e %8.3f        %.4f"
              % (d, l, sig, float(g), float(g) * 2 ** (l / 2), 2.0 ** (1 - l),
                 delta_cap(l), float(g) * 2 ** (l - 1),
                 float(gthm) * 2 ** (l / 2)))
    print("  first l with a violator above 2^(1-l): %s" % first_beat)
    check(first_beat is not None, "a violator above 2^(1-l) is found")
    # the explicit family for all l, from the closed form only
    worst = min(float(thm_gamma(l)[0]) * 2 ** (l / 2) for l in range(8, 200))
    check(all(thm_gamma(l)[1] for l in range(4, 200)), "inequality l=4..199")
    check(worst >= 1 / 32, "gamma_thm >= 2^(-l/2)/32 for l = 8..199")
    lim = float(thm_gamma(199)[0]) * 2 ** (199 / 2)
    print("  closed form, sigma = floor(2^(l/2)): inequality holds l = 4..199;"
          " min gamma_thm 2^(l/2) over l = 8..199 is %.4f; at l = 199 it is"
          " %.5f (limit 1/16 = 0.0625 for even l)" % (worst, lim))
    return first_beat


def part_D():
    print("Part D: K4 on {0,e1,e2,e3} at d = 3")
    d = 3
    Sp = [0, 1, 2, 4]
    edge = sidon_graph(d, Sp)
    lines = lines_of(d)
    tc = type_counts(d, edge, lines)
    v, D0 = graph_val_D(d, edge, best_cosets(d, edge, lines), lines)
    check(tc == {"FT": 4, "FU": 0, "t": 3, "s1": 0}, "K4 types")
    check(v == Fr(1, 2) + Fr(1, 7) and D0 == Fr(1, 7), "K4 gamma = 1/7")
    print("  types %s, val = %s = 1/2 + 1/7, D = %s" % (tc, v, D0))


# ------------------------------------------------------------ lift to n > l+1
def lift_tables(d, n, edge, choice):
    """F(S) = F0(phi S) o phi if S meets K = ker(phi) trivially, else 0."""
    l = d - 1
    mask = (1 << d) - 1
    lines = lines_of(d)
    S0s = subspaces(d, l)
    W0s = subspaces(d, l - 1)
    S0_of = {max(perp(d, S)): S for S in S0s}
    xS0 = {S0_of[c]: edge[c][0] for c in edge}
    xW0 = {W: choice[tuple(sorted(perp(d, W) - {0}))] for W in W0s}
    Ss = subspaces(n, l)
    Ws = subspaces(n, l - 1)

    def lift(T, table):
        if any(t and not (t & mask) for t in T):
            return 0, False
        return table[frozenset(t & mask for t in T)], True

    xS = {S: lift(S, xS0)[0] for S in Ss}
    xW = {}
    ninj = 0
    for W in Ws:
        xW[W], inj = lift(W, xW0)
        ninj += inj
    return xS, xW, Ws, Fr(ninj, len(Ws))


def p_inj_formula(n, l):
    k = n - l - 1
    p = Fr(1)
    for i in range(l - 1):
        p *= Fr((1 << n) - (1 << (k + i)), (1 << n) - (1 << i))
    return p


def part_E():
    print("Part E: lift of a codim-1 table to n > l+1 (primal brute force)")
    cases = [(3, 4, [0, 1, 2, 4]), (3, 5, [0, 1, 2, 4]),
             (4, 5, None), (4, 6, None)]
    for d, n, Sp in cases:
        l = d - 1
        if Sp is None:
            G = apn_set(d // 2)
            Sp = max((G[:s] for s in range(3, len(G) + 1)),
                     key=lambda S: gamma_star(sidon_counts(d, S))[0])
        edge = sidon_graph(d, Sp)
        lines = lines_of(d)
        choice = best_cosets(d, edge, lines)
        v0, D0 = graph_val_D(d, edge, choice, lines)
        xS, xW, Ws, pinj = lift_tables(d, n, edge, choice)
        check(pinj == p_inj_formula(n, l), "p_inj formula n=%d l=%d" % (n, l))
        check(pinj >= Fr(3, 4), "p_inj >= 3/4")
        v, D = primal_val_D(n, l, xS, xW, Ws)
        lb_v = (1 - pinj) * (1 - Fr(1 << (l - 1), 1 << n)) + pinj * v0
        check(v >= lb_v, "lift val lower bound n=%d l=%d" % (n, l))
        check(D >= pinj * D0, "lift D lower bound n=%d l=%d" % (n, l))
        g0 = min(v0 - Fr(1, 2), D0)
        g = min(v - Fr(1, 2), D)
        if g0 > 0:
            check(g >= pinj * g0, "lifted violator n=%d l=%d" % (n, l))
        print("  (n,l)=(%d,%d) from d=%d, |S'|=%d: p_inj=%s; codim-1 val=%s"
              " D=%s; lifted val=%s D=%s; gamma_lift=%s >= p_inj*gamma0=%s"
              % (n, l, d, len(Sp), pinj, v0, D0, v, D, g, pinj * g0))


def main():
    dmax = int(sys.argv[1]) if len(sys.argv) > 1 else 20
    part_A()
    part_B()
    part_C(dmax)
    part_D()
    part_E()
    if FAIL:
        print("%d checks FAILED" % len(FAIL))
        sys.exit(1)
    print("all checks passed")


if __name__ == "__main__":
    main()
