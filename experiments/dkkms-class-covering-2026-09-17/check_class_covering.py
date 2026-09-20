#!/usr/bin/env python3
"""Checks for dkkms-quotient-covering-proves-99-percent-rigidity.

Part A  exact image law of the DKKMS seed L' in Y = X_U / H_U, small (k, d):
        (i)  given V and L' meet H_U = 0, the image is uniform on Gr(W_V, d);
        (ii) exact chi-square of mu_U against uniform on Gr(Y, d) equals the
             Gaussian-binomial formula and is below the product bound;
        (iii) TV(mu_P, uniform) <= (1/2) sqrt(chi*) + 2^(d-k).
Part B  the per-tuple two-extension rejection of G_multi, computed at the
        level of X_U by brute force, equals the rejection computed from the
        image triple (Qbar, Sbar_1, Sbar_2) alone, for random class tables.
Part C  SD^cl at every admissible DKKMS point: the least l_0 with
        SD^cl(l, k) <= 1e-5 for all k >= k_A(l), q = 1, both log readings.

Deterministic; seed 20260920.  Runs in about a minute.
"""
import itertools
import math
import random

random.seed(20260920)


# ---------------------------------------------------------------- F_2 helpers
def span(vecs):
    s = {0}
    for v in vecs:
        s |= {x ^ v for x in s}
    return s


def subspaces(basis, d):
    """All d-subspaces of span(basis), as frozensets of nonzero vectors."""
    elems = sorted(span(basis) - {0})
    out = set()
    for combo in itertools.combinations(elems, d):
        sp = span(combo)
        if len(sp) == 2 ** d:
            out.add(frozenset(sp - {0}))
    return out


def gauss(n, d):
    if d < 0 or d > n:
        return 0
    num = den = 1
    for i in range(d):
        num *= 2 ** (n - i) - 1
        den *= 2 ** (d - i) - 1
    return num // den


def pi(x, k):
    """X_U = F_2^(3k) -> Y = F_2^(2k), kernel spanned by the block 111 vectors."""
    y = 0
    for i in range(k):
        a, b, c = (x >> 3 * i) & 1, (x >> (3 * i + 1)) & 1, (x >> (3 * i + 2)) & 1
        y |= (a ^ c) << (2 * i) | (b ^ c) << (2 * i + 1)
    return y


def H_basis(k):
    return [7 << 3 * i for i in range(k)]


def configs(k, beta, nus):
    """Law of V given U: per block 'K' (kept) or a variable index v."""
    for cfg in itertools.product(['K', 0, 1, 2], repeat=k):
        w = 1.0
        for i, c in enumerate(cfg):
            w *= (1 - beta) if c == 'K' else beta * nus[i][c]
        if w > 0:
            yield cfg, w


def XV_basis(cfg):
    b = []
    for i, c in enumerate(cfg):
        if c == 'K':
            b += [1 << 3 * i, 1 << (3 * i + 1), 1 << (3 * i + 2)]
        else:
            b.append(1 << (3 * i + c))
    return b


# ---------------------------------------------------------------- Part A
def part_A():
    print("Part A: image law of L' in Gr(Y, d)")
    worst_ratio = 0.0
    for (k, d) in [(2, 1), (3, 1), (4, 1), (3, 2)]:  # d < k
        H = span(H_basis(k))
        for beta in (0.1, 0.35, 0.7):
            for nuname, nu in (("unif", (1 / 3, 1 / 3, 1 / 3)), ("skew", (0.6, 0.3, 0.1))):
                nus = [nu] * k
                muU, muP = {}, {}
                cache = {}
                pairs = []
                for cfg, w in configs(k, beta, nus):
                    key = cfg
                    sub = subspaces(XV_basis(cfg), d)
                    good = [S for S in sub if not (S & H)]
                    imgs = {}
                    for S in good:
                        Q = frozenset(pi(x, k) for x in S)
                        imgs[Q] = imgs.get(Q, 0) + 1
                    dimW = sum(2 if c == 'K' else 1 for c in cfg)
                    # (i) uniform on Gr(W_V, d)
                    assert len(imgs) == gauss(dimW, d), (k, d, cfg)
                    assert len(set(imgs.values())) == 1, (k, d, cfg)
                    pE = len(good) / len(sub)
                    for Q in imgs:
                        muU[Q] = muU.get(Q, 0) + w / len(imgs)
                        muP[Q] = muP.get(Q, 0) + w * pE / len(imgs)
                    pairs.append((cfg, w, dimW))
                ZP = sum(muP.values())
                GY = gauss(2 * k, d)
                chi = sum(p * p for p in muU.values()) * GY - 1
                # (ii) Gaussian-binomial formula
                form = 0.0
                for (c1, w1, a1) in pairs:
                    for (c2, w2, a2) in pairs:
                        inter = 0
                        for x, y in zip(c1, c2):
                            if x == 'K' and y == 'K':
                                inter += 2
                            elif x == 'K' or y == 'K' or x == y:
                                inter += 1
                        form += w1 * w2 * GY * gauss(inter, d) / (gauss(a1, d) * gauss(a2, d))
                form -= 1
                s_i = sum(v * v for v in nu)
                prod = (1 + beta ** 2 * s_i * (2 ** d - 1)) ** k
                bound = (1 - 2.0 ** (d - k)) ** -2 * prod - 1
                tv = 0.5 * sum(abs(muP.get(Q, 0) / ZP - 1 / GY) for Q in
                               set(muP) | set(subspaces(list(1 << j for j in range(2 * k)), d)))
                tvb = 0.5 * math.sqrt(max(bound, 0)) + 2.0 ** (d - k)
                assert abs(chi - form) < 1e-9, (chi, form)
                assert chi <= bound + 1e-12 and tv <= tvb + 1e-12
                worst_ratio = max(worst_ratio, tv / tvb)
                print(f"  k={k} d={d} beta={beta:4} nu={nuname}: chi={chi:.5f} "
                      f"formula={form:.5f} bound={bound:.5f}  TV={tv:.4f} <= {tvb:.4f}")
    print(f"  all assertions hold; worst TV/bound = {worst_ratio:.3f}")


# ---------------------------------------------------------------- Part B
def functional_on(S, rnd):
    """Random linear functional on the subspace S (frozenset of nonzero vectors)."""
    basis = []
    sp = {0}
    for v in sorted(S):
        if v not in sp:
            basis.append(v)
            sp |= {x ^ v for x in sp}
    val = {0: 0}
    for v in basis:
        r = rnd.randrange(2)
        val.update({x ^ v: val[x] ^ r for x in list(val)})
    return val


def part_B(trials=6):
    print("Part B: two-extension rejection, X_U level vs image level (l = 2)")
    k, l = 2, 2
    n = 3 * k
    H = span(H_basis(k))
    Y_planes = subspaces([1 << j for j in range(2 * k)], l)
    worst = 0.0
    for t in range(trials):
        rnd = random.Random(1000 + t)
        beta = rnd.choice([0.2, 0.5, 0.8])
        nus = [(0.5, 0.3, 0.2)] * k
        b = [rnd.randrange(2) for _ in range(k)]

        def hstar(z):
            return sum(b[i] * ((z >> 3 * i) & 1) for i in range(k)) & 1

        F = {S: functional_on(S, rnd) for S in Y_planes}

        def A(u, x, z):
            S = frozenset(span([pi(u, k), pi(x, k)]) - {0})
            return F[S][pi(z, k)] ^ hstar(z)

        # X_U level: (V, u) weighted by G_multi, x1, x2 uniform valid extensions
        rejX = 0.0
        tot = 0.0
        muP = {}
        for cfg, w in configs(k, beta, nus):
            XV = sorted(span(XV_basis(cfg)) - {0})
            for u in XV:
                if u in H:
                    continue
                LH = {h ^ e for h in H for e in (0, u)}
                valid = [x for x in range(1 << n) if x not in LH]
                wt = w / len(XV) * len(valid) / (2 ** n - 2)
                vals = [A(u, x, u) for x in valid]
                p1 = sum(vals) / len(valid)
                rejX += wt * 2 * p1 * (1 - p1)
                tot += wt
                q = pi(u, k)
                muP[q] = muP.get(q, 0) + wt
        rejX /= tot
        # image level: q ~ muP, ybar1, ybar2 uniform in Y \ <q>
        rejY = 0.0
        rejT = 0.0
        Yn = [y for y in range(1, 1 << 2 * k)]
        for q in Yn:
            ext = [y for y in Yn if y != q]
            vals = [F[frozenset({q, y, q ^ y})][q] for y in ext]
            p1 = sum(vals) / len(ext)
            r = 2 * p1 * (1 - p1)
            rejY += muP.get(q, 0) / tot * r
            rejT += r / len(Yn)
        tvq = 0.5 * sum(abs(muP.get(q, 0) / tot - 1 / len(Yn)) for q in Yn)
        assert abs(rejX - rejY) < 1e-12, (rejX, rejY)
        assert abs(rejX - rejT) <= tvq + 1e-12
        worst = max(worst, abs(rejX - rejY))
        print(f"  trial {t}: beta={beta} rej_X={rejX:.6f} rej_image={rejY:.6f} "
              f"rej_T(Y)={rejT:.6f} TV(Qbar)={tvq:.4f}")
    print(f"  X-level and image-level rejections agree to {worst:.1e}")


# ---------------------------------------------------------------- Part C
def lnlnk_reading(lnk, base2):
    """log log k in the natural or the base-2 reading, from ln k."""
    if base2:
        return math.log2(lnk / math.log(2))
    return math.log(lnk)


def SDcl(l, lnk, base2=False, s=1.0):
    """SD^cl = (1/2) sqrt(chi*) + 3 * 2^(l-k), computed from ln k (k may be huge)."""
    logx = 2 * math.log(lnlnk_reading(lnk, base2)) + math.log(s) \
        + (l - 1) * math.log(2) + math.log1p(-2.0 ** (1 - l)) - lnk
    x = math.exp(logx)
    k = math.exp(lnk) if lnk < 700 else float('inf')
    eps = 2.0 ** (l - 1 - k) if k - l < 1000 else 0.0
    chi = math.expm1(x - 2 * math.log1p(-eps))
    tail = 3 * 2.0 ** (l - k) if k - l < 1000 else 0.0
    return 0.5 * math.sqrt(chi) + tail


def SDstar(l, lnk, base2=False):
    k = math.exp(lnk) if lnk < 700 else float("inf")
    tail = 3 * 2.0 ** (l - k) if k - l < 1000 else 0.0
    return lnlnk_reading(lnk, base2) * math.exp(-lnk / 2 + (l + 3) * math.log(2)) + tail


def lnkA(l, q=1.0):
    """ln of k_A(l,q) = e^(ql) (2 l ln 2 + ln(4 * 192^2))."""
    return q * l + math.log(2 * l * math.log(2) + math.log(4 * 192 ** 2))


def part_C():
    print("Part C: SD^cl at admissible DKKMS points (threshold 1e-5)")
    for base2 in (False, True):
        for s in (1.0, 1 / 3):
            vals = [(l, SDcl(l, lnkA(l), base2, s)) for l in range(3, 3000)]
            bad = [l for l, v in vals if v > 1e-5]
            l0 = max(bad) + 1
            dec = all(vals[i + 1][1] <= vals[i][1] for i in range(len(vals) - 1)
                      if vals[i][0] >= l0)
            mono = True
            for l in range(l0, 3000, 37):
                v = [SDcl(l, lnkA(l) + j * 0.5, base2, s) for j in range(0, 400)]
                mono &= all(v[i + 1] <= v[i] for i in range(len(v) - 1))
            print(f"  reading={'log2' if base2 else 'ln  '} s_i<={s:.3f}: l_0 = {l0}, "
                  f"SD^cl(l_0,k_A)={SDcl(l0, lnkA(l0), base2, s):.3e}, "
                  f"decreasing in l on [l_0,3000): {dec}, decreasing in k: {mono}")
    for l in (60, 90, 120):
        lk = lnkA(l)
        lk0 = lk
        while SDstar(l, lk0) > 1e-5:
            lk0 += 0.01
        t = lnlnk_reading(lk, False) * math.exp(-lk / 2) * 2 ** (l / 2) / math.sqrt(l)
        print(f"  l={l}: ln k_A={lk:.2f}, SD*(k_A)={SDstar(l, lk):.3e}, "
              f"SD^cl(k_A)={SDcl(l, lk):.3e}, SD*<=1e-5 needs ln k >= {lk0:.2f}; "
              f"t(k_A)={t:.3e}")
    for q in (0.8, 0.75, 0.72):
        bad = [l for l in range(3, 20000) if SDcl(l, lnkA(l, q)) > 1e-5]
        print(f"  real advice constant q={q}: SD^cl(l, k_A(l,q)) <= 1e-5 for every "
              f"l in ({max(bad) if bad else 2}, 20000)")


if __name__ == "__main__":
    part_A()
    part_B()
    part_C()
