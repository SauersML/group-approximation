"""Checks for one-sided-three-shear-lamp-criterion-drops-the-torus.

M = F_p[t]^2 (column vectors). A character chi of M is a pair (alpha, beta) in
(F_p^N)^2 with chi(a, b) = sum_k a_k alpha_k + b_k beta_k. The group acts by
(gamma . chi)(m) = chi(gamma^-1 m).

iota(alpha) = sum_k alpha_k t^(-k-1) identifies F_p^N with O = t^-1 F_p[[t^-1]].
U_N = {alpha_k = beta_k = 0 for k < N}. d(x, y) = deg x - deg y.

Checked here, for p = 2, 3, 5:
  (A) on U_2, the dual action of each generator equals the K-linear map
      A = (gamma^-1)^T applied to iota(chi), with no polynomial part;
  (B) sector inclusions:
      e_21(t) maps {d <= 0} into {d = 1},
      e_12(t) maps {d >= 0} into {d = -1},
      e_12(1) maps {d = 1} into {d = 0};
  (C) general degrees: e_21(s), deg s = a >= 1, maps {d <= 0} into {d = a};
      e_12(r), deg r = b >= 1, maps {d >= 0} into {d = -b};
      e_12(u), deg u = c >= 0, maps {d = a} into {d = -c};
      e_21(u), deg u = c >= 0, maps {d = -b} into {d = c};
  (D) generation: t^k e_i is a Z-combination of Gamma_0-translates of e_1, e_2.
"""
import random

W = 48  # window length for characters


def padd(f, g, p):
    n = max(len(f), len(g))
    return [((f[i] if i < len(f) else 0) + (g[i] if i < len(g) else 0)) % p for i in range(n)]


def pmul(f, g, p):
    if not f or not g:
        return []
    out = [0] * (len(f) + len(g) - 1)
    for i, a in enumerate(f):
        if a:
            for j, b in enumerate(g):
                out[i + j] = (out[i + j] + a * b) % p
    return out


def pneg(f, p):
    return [(-a) % p for a in f]


def e12(r):
    return [[[1], r], [[], [1]]]


def e21(r):
    return [[[1], []], [r, [1]]]


def inv_unipotent(g, p):
    # inverse of e12(r) is e12(-r), of e21(r) is e21(-r)
    return [[g[0][0], pneg(g[0][1], p)], [pneg(g[1][0], p), g[1][1]]]


def mat_vec(g, v, p):
    return [padd(pmul(g[0][0], v[0], p), pmul(g[0][1], v[1], p), p),
            padd(pmul(g[1][0], v[0], p), pmul(g[1][1], v[1], p), p)]


def transpose(g):
    return [[g[0][0], g[1][0]], [g[0][1], g[1][1]]]


def pair(v, chi, p):
    al, be = chi
    s = 0
    for k, a in enumerate(v[0]):
        s += a * al[k]
    for k, b in enumerate(v[1]):
        s += b * be[k]
    return s % p


def dual_action(g, chi, p, K):
    """(g.chi)(t^k e_i) for k < K, computed by the pairing."""
    gi = inv_unipotent(g, p)
    al, be = [], []
    for k in range(K):
        mono = [0] * k + [1]
        al.append(pair(mat_vec(gi, [mono, []], p), chi, p))
        be.append(pair(mat_vec(gi, [[], mono], p), chi, p))
    return al, be


def series_mul_poly(f, alpha, p):
    """poly f times iota(alpha); returns dict exponent -> coef."""
    out = {}
    for i, a in enumerate(f):
        if a:
            for k, c in enumerate(alpha):
                if c:
                    e = i - k - 1
                    out[e] = (out.get(e, 0) + a * c) % p
    return out


def k_linear(g, chi, p):
    A = transpose(inv_unipotent(g, p))
    al, be = chi
    res = []
    for row in A:
        s = {}
        for f, comp in ((row[0], al), (row[1], be)):
            for e, c in series_mul_poly(f, comp, p).items():
                s[e] = (s.get(e, 0) + c) % p
        res.append({e: c for e, c in s.items() if c})
    return res


def deg_seq(seq):
    for k, c in enumerate(seq):
        if c:
            return -k - 1
    return None  # -infinity


def dval(chi):
    dx, dy = deg_seq(chi[0]), deg_seq(chi[1])
    if dx is None and dy is None:
        return 'zero'
    if dx is None:
        return float('-inf')
    if dy is None:
        return float('inf')
    return dx - dy


def rand_chi(p, lead_a, lead_b):
    """character in U_2 with first nonzero entries at lead_a, lead_b (None = zero)."""
    def comp(lead):
        v = [0] * W
        if lead is None:
            return v
        v[lead] = random.randrange(1, p)
        for k in range(lead + 1, W):
            v[k] = random.randrange(p)
        return v
    return comp(lead_a), comp(lead_b)


def rand_poly(p, deg):
    f = [random.randrange(p) for _ in range(deg)] + [random.randrange(1, p)]
    return f


def act(g, chi, p):
    return dual_action(g, chi, p, W - 8)


def trunc(chi, K):
    return chi[0][:K], chi[1][:K]


def main():
    random.seed(20260917)
    report = []
    for p in (2, 3, 5):
        gens = {'e12(1)': e12([1]), 'e12(t)': e12([0, 1]), 'e21(t)': e21([0, 1])}
        # (A)
        bad_a = 0
        for _ in range(300):
            la = random.choice([None] + list(range(2, 20)))
            lb = random.choice(list(range(2, 20))) if la is None else random.choice([None] + list(range(2, 20)))
            chi = rand_chi(p, la, lb)
            for g in gens.values():
                dual = act(g, chi, p)
                kl = k_linear(g, chi, p)
                for comp in range(2):
                    if any(e >= 0 for e in kl[comp]):
                        bad_a += 1
                    for k in range(W - 8):
                        if dual[comp][k] != kl[comp].get(-k - 1, 0):
                            bad_a += 1
        # (B)
        bad_b = 0
        tested = {'d<=0': 0, 'd>=0': 0, 'd=1': 0}
        for _ in range(2000):
            la = random.choice([None] + list(range(2, 18)))
            lb = random.choice(list(range(2, 18))) if la is None else random.choice([None] + list(range(2, 18)))
            chi = rand_chi(p, la, lb)
            d = dval(chi)
            if d <= 0:
                tested['d<=0'] += 1
                if dval(trunc(act(gens['e21(t)'], chi, p), W - 8)) != 1:
                    bad_b += 1
            if d >= 0:
                tested['d>=0'] += 1
                if dval(trunc(act(gens['e12(t)'], chi, p), W - 8)) != -1:
                    bad_b += 1
            if d == 1:
                tested['d=1'] += 1
                if dval(trunc(act(gens['e12(1)'], chi, p), W - 8)) != 0:
                    bad_b += 1
        # (C)
        bad_c, tested_c = 0, 0
        for _ in range(600):
            a, b, c = random.randint(1, 3), random.randint(1, 3), random.randint(0, 3)
            s, r, u = rand_poly(p, a), rand_poly(p, b), rand_poly(p, c)
            la = random.choice([None] + list(range(6, 16)))
            lb = random.choice(list(range(6, 16))) if la is None else random.choice([None] + list(range(6, 16)))
            chi = rand_chi(p, la, lb)
            d = dval(chi)
            K = W - 12
            if d <= 0:
                tested_c += 1
                bad_c += dval(trunc(dual_action(e21(s), chi, p, K), K)) != a
            if d >= 0:
                tested_c += 1
                bad_c += dval(trunc(dual_action(e12(r), chi, p, K), K)) != -b
            if d == a:
                tested_c += 1
                bad_c += dval(trunc(dual_action(e12(u), chi, p, K), K)) != -c
            if d == -b:
                tested_c += 1
                bad_c += dval(trunc(dual_action(e21(u), chi, p, K), K)) != c
        # (D) generation, exact
        bad_d = 0
        v1, v2 = [[1], []], [[], [1]]
        cur = [v1, v2]
        for k in range(1, 12):
            nxt = []
            for v in cur:
                if v[0] and any(v[0]):
                    w = mat_vec(e21([0, 1]), v, p)
                    diff = [padd(w[0], pneg(v[0], p), p), padd(w[1], pneg(v[1], p), p)]
                else:
                    w = mat_vec(e12([0, 1]), v, p)
                    diff = [padd(w[0], pneg(v[0], p), p), padd(w[1], pneg(v[1], p), p)]
                nxt.append(diff)
            cur = nxt
            got = sorted((tuple(x[0]), tuple(x[1])) for x in cur)
            mono = tuple([0] * k + [1])
            want = sorted([((), mono), (mono, ())])
            strip = lambda t: tuple(t[:max([i + 1 for i, c in enumerate(t) if c] or [0])])
            got = sorted((strip(x), strip(y)) for x, y in got)
            if got != want:
                bad_d += 1
        report.append(f"p={p}: (A) dual action = K-linear on U_2: mismatches {bad_a}")
        report.append(f"p={p}: (B) sector inclusions tested {tested}: failures {bad_b}")
        report.append(f"p={p}: (C) general-degree inclusions tested {tested_c}: failures {bad_c}")
        report.append(f"p={p}: (D) t^k e_i, k<12, from Gamma_0-differences: failures {bad_d}")
    # negative control: without restricting to U_2 the action truncates
    p = 3
    chi = ([0] * W, [0] * W)
    chi[1][0] = 1  # beta = t^-1, deg -1: e21(t) adds t*beta (degree 0) to alpha
    kl = k_linear(e21([0, 1]), chi, p)
    report.append("control: chi = (0, t^-1) outside U_2, K-linear image has polynomial part: "
                  + str(any(e >= 0 for e in kl[0])))
    print("\n".join(report))


if __name__ == '__main__':
    main()
