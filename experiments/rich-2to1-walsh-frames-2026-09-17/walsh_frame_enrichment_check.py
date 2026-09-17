#!/usr/bin/env python3
"""Checks for walsh-frame-rich-2to1-sdp-gaps-have-value-near-one.

Setting: the label vectors at a left vertex u are x_(u,a) = f_u * chi_(psi_u(a)) / K
in R^(F_2^k), where K = 2^k, f_u : F_2^k -> {+-1} with f_u(0) = 1, and psi_u is a
bijection [K] -> F_2^k. A perfect basic-SDP solution forces
y_(v,b) = x_(u,a) + x_(u,a') on every edge (u,v) with pi_(uv)^(-1)(b) = {a, a'}.

Vectors are kept unnormalised (times K) as integer tuples.

  A  pair-sum identity: an f_g admits a pairing with the same pair sums as
     (f_u = 1, P) iff f_g is linear on gamma^perp for every difference gamma
     of P; if Gamma(P) is 2-hitting, those f_g are exactly the characters.
     Exhaustive for k = 3 (direct vector comparison), all pairings sampled at
     k = 4 (vector comparison on a subsample, restriction test on all f_g).
  B  hyperplane-character lemma is sharp: for k = 3 and every nonempty set
     Gamma of nonzero vectors, "linear on every gamma^perp, gamma in Gamma"
     forces linearity iff Gamma is 2-hitting.
  C  p_K = Pr[uniform pairing of F_2^k is not 2-hitting]: exact for k = 3, 4,
     Monte Carlo for k = 5..10, against the analytic bound
     ((K-1)(K-2)/6) * prod_(j < ceil(m/2)) (3m-j)/(4m-1-2j), m = K/4.
  D  rigid labelling: random Walsh-frame games with perfect SDP solutions,
     including cross-frame right vertices; the component labelling satisfies
     every edge at a good (2-hitting) right vertex.
"""

import itertools
import math
import random
import sys

random.seed(20260917)


def chi(c, x):
    return -1 if bin(c & x).count("1") & 1 else 1


def all_pairings(elems):
    if not elems:
        yield []
        return
    a = elems[0]
    rest = elems[1:]
    for i in range(len(rest)):
        b = rest[i]
        for p in all_pairings(rest[:i] + rest[i + 1:]):
            yield [(a, b)] + p


def random_pairing(K):
    perm = list(range(K))
    random.shuffle(perm)
    return [(perm[2 * i], perm[2 * i + 1]) for i in range(K // 2)]


def dot(a, b):
    return bin(a & b).count("1") & 1


def codim2_masks(k):
    """Bitmasks (over F_2^k) of all codimension-2 subspaces {x,y}^perp."""
    K = 1 << k
    masks = set()
    for x in range(1, K):
        for y in range(x + 1, K):
            m = 0
            for z in range(K):
                if dot(z, x) == 0 and dot(z, y) == 0:
                    m |= 1 << z
            masks.add(m)
    return sorted(masks)


def is_two_hitting(gamma_mask, masks):
    return all(gamma_mask & m for m in masks)


def diff_mask(P):
    m = 0
    for a, b in P:
        m |= 1 << (a ^ b)
    return m


def is_linear(H, k):
    """H : list of 0/1 over F_2^k; linear iff H(x) = sum x_i H(e_i)."""
    K = 1 << k
    for x in range(K):
        s = 0
        for i in range(k):
            if x >> i & 1:
                s ^= H[1 << i]
        if s != H[x]:
            return False
    return True


def linear_on_hyperplane(H, gamma, k):
    """H restricted to gamma^perp is additive (H(0) = 0 assumed)."""
    K = 1 << k
    hp = [x for x in range(K) if dot(x, gamma) == 0]
    for x in hp:
        for y in hp:
            if H[x ^ y] != H[x] ^ H[y]:
                return False
    return True


def frame_vec(f, c, K):
    return tuple(f[x] * chi(c, x) for x in range(K))


def pair_sum(f, a, b, K):
    return tuple(f[x] * (chi(a, x) + chi(b, x)) for x in range(K))


def admits_same_pair_sums(f_g, P, K):
    """Direct vector test: is there a pairing P' at g with
    f_g chi_c + f_g chi_c' = chi_a + chi_b for each (a,b) in P, P' a pairing?"""
    sums = {}
    for a in range(K):
        for b in range(a + 1, K):
            sums[pair_sum(f_g, a, b, K)] = (a, b)
    one = [1] * K
    used = set()
    for a, b in P:
        y = pair_sum(one, a, b, K)
        if y not in sums:
            return False
        a2, b2 = sums[y]
        if a2 in used or b2 in used:
            return False
        used.add(a2)
        used.add(b2)
    return len(used) == K


def functions_with_f0_one(k):
    K = 1 << k
    for bits in range(1 << (K - 1)):
        yield [1] + [(-1 if bits >> (x - 1) & 1 else 1) for x in range(1, K)]


def restriction_tables(k):
    """lin[gamma] = set of restriction bitmasks of characters to gamma^perp."""
    K = 1 << k
    hps = {g: [x for x in range(K) if dot(x, g) == 0] for g in range(1, K)}
    lin = {}
    for g, hp in hps.items():
        s = set()
        for c in range(K):
            m = 0
            for i, x in enumerate(hp):
                if chi(c, x) == -1:
                    m |= 1 << i
            s.add(m)
        lin[g] = s
    return hps, lin


def restricted_linear(f, g, hps, lin):
    m = 0
    for i, x in enumerate(hps[g]):
        if f[x] == -1:
            m |= 1 << i
    return m in lin[g]


def characters(k):
    K = 1 << k
    return {tuple(chi(c, x) for x in range(K)) for c in range(K)}


def check_A(k, n_pairings, n_direct, exhaustive):
    K = 1 << k
    masks = codim2_masks(k)
    hps, lin = restriction_tables(k)
    chars = characters(k)
    funcs = [tuple(f) for f in functions_with_f0_one(k)]
    # bitset over funcs of the frames that are linear on gamma^perp
    bits = {}
    for g in range(1, K):
        b = 0
        for i, f in enumerate(funcs):
            if restricted_linear(f, g, hps, lin):
                b |= 1 << i
        bits[g] = b
    full = (1 << len(funcs)) - 1
    if exhaustive:
        pairings = list(all_pairings(list(range(K))))
    else:
        pairings = [random_pairing(K) for _ in range(n_pairings)]
    stats = {"two_hitting": 0, "not_two_hitting": 0, "extra_frames_when_not": 0}
    for idx, P in enumerate(pairings):
        gammas = sorted({a ^ b for a, b in P})
        vb = full
        for g in gammas:
            vb &= bits[g]
        valid = [funcs[i] for i in range(len(funcs)) if vb >> i & 1]
        if idx < n_direct:
            sample = valid + random.sample(funcs, min(len(funcs), 60))
            for f in sample:
                direct = admits_same_pair_sums(f, P, K)
                restr = all(restricted_linear(f, g, hps, lin) for g in gammas)
                assert direct == restr, ("pair-sum test mismatch", k, P, f)
        assert (set(valid) == chars) == forcing(k, gammas), ("forcing mismatch", P)
        if set(valid) == chars:
            stats["only_characters"] = stats.get("only_characters", 0) + 1
        if is_two_hitting(diff_mask(P), masks):
            stats["two_hitting"] += 1
            assert set(valid) == chars, ("2-hitting but non-character frame", P)
        else:
            stats["not_two_hitting"] += 1
            if set(valid) != chars:
                stats["extra_frames_when_not"] += 1
    return len(pairings), stats


def forcing(k, gammas):
    """GF(2) test: the only H (H(0) = 0) additive on every gamma^perp are linear.
    Variables H(1..K-1); rows e_x + e_y + e_(x+y) for x != y nonzero in gamma^perp."""
    K = 1 << k
    basis = {}  # pivot -> row
    for g in gammas:
        hp = [x for x in range(1, K) if dot(x, g) == 0]
        for i, x in enumerate(hp):
            for y in hp[i + 1:]:
                r = (1 << x) | (1 << y) | (1 << (x ^ y))
                while r:
                    p = r.bit_length() - 1
                    if p in basis:
                        r ^= basis[p]
                    else:
                        basis[p] = r
                        break
    return (K - 1) - len(basis) == k


def check_B():
    """k = 3, all nonempty Gamma: brute force forcing == GF(2) forcing, and
    2-hitting => forcing. 2-hitting is sufficient, not necessary."""
    k, K = 3, 8
    masks = codim2_masks(k)
    Hs = [[0] + [(bits >> (x - 1)) & 1 for x in range(1, K)]
          for bits in range(1 << (K - 1))]
    counts = {"sets": 0, "forcing": 0, "two_hitting": 0}
    for gmask in range(1, 1 << (K - 1)):
        Gamma = [x for x in range(1, K) if gmask >> (x - 1) & 1]
        gm = 0
        for x in Gamma:
            gm |= 1 << x
        forced = True
        for H in Hs:
            if all(linear_on_hyperplane(H, g, k) for g in Gamma):
                if not is_linear(H, k):
                    forced = False
                    break
        assert forced == forcing(k, Gamma), ("GF(2) test mismatch", Gamma)
        th = is_two_hitting(gm, masks)
        if th:
            assert forced, ("2-hitting but not forcing", Gamma)
        counts["sets"] += 1
        counts["forcing"] += forced
        counts["two_hitting"] += th
    return counts


def exact_p(k):
    K = 1 << k
    masks = codim2_masks(k)
    cache = {}
    total = [0, 0, 0]

    def rec(remaining, gm):
        if not remaining:
            if gm not in cache:
                gammas = [x for x in range(1, K) if gm >> x & 1]
                cache[gm] = (is_two_hitting(gm, masks), forcing(k, gammas))
            total[0] += 1
            if not cache[gm][0]:
                total[1] += 1
            if not cache[gm][1]:
                total[2] += 1
            return
        a = remaining[0]
        rest = remaining[1:]
        for i in range(len(rest)):
            rec(rest[:i] + rest[i + 1:], gm | (1 << (a ^ rest[i])))

    rec(tuple(range(K)), 0)
    return total[0], total[1], total[2]


def exposure_product(K):
    """prod_(j < ceil(m/2)) (3m - j)/(4m - 1 - 2j), m = K/4."""
    m = K // 4
    prod = 1.0
    for j in range(math.ceil(m / 2)):
        prod *= (3 * m - j) / (4 * m - 1 - 2 * j)
    return prod


def analytic_bound(K):
    return (K - 1) * (K - 2) / 6 * exposure_product(K)


def single_coset_avoid(K, m, trials):
    """Monte Carlo: the fixed m-set {0..m-1} contains no pair."""
    bad = 0
    for _ in range(trials):
        P = random_pairing(K)
        if all(not (a < m and b < m) for a, b in P):
            bad += 1
    return bad / trials


def check_C(max_k, trials):
    rows = []
    for k in range(3, max_k + 1):
        K = 1 << k
        m = K // 4
        if k <= 4:
            n, nb, nf = exact_p(k)
            p = nb / n
            kind = "exact: not 2-hitting %d/%d, not forcing %d/%d" % (nb, n, nf, n)
        elif k <= 7:
            masks = codim2_masks(k)
            nb = nf = 0
            for _ in range(trials):
                P = random_pairing(K)
                th = is_two_hitting(diff_mask(P), masks)
                fo = forcing(k, sorted({a ^ b for a, b in P})) if k <= 6 else th
                assert fo or not th
                nb += not th
                nf += not fo
            p = nb / trials
            kind = "MC: not 2-hitting %d/%d, not forcing %d/%d%s" % (
                nb, trials, nf, trials, "" if k <= 6 else " (forcing not run)")
        else:
            p = None
            kind = "bound only"
        b = analytic_bound(K)
        if p is not None and b < 1:
            assert p <= b + 3 * math.sqrt(max(p, 1e-9) / trials), (k, p, b)
        if m >= 2 and k <= 6:
            sc = single_coset_avoid(K, m, trials)
            prod = exposure_product(K)
            assert sc <= prod + 3 * math.sqrt(max(sc, 1e-9) / trials), (k, sc, prod)
        if m >= 8:
            assert exposure_product(K) <= (7 / 8) ** (K / 8) + 1e-15, K
        rows.append((k, K, kind, p, b))
    return rows


def check_D(k, n_left, n_right, max_deg):
    """Random Walsh-frame games with a perfect SDP solution; rigid labelling."""
    K = 1 << k
    masks = codim2_masks(k)
    hps, lin = restriction_tables(k)
    one = tuple([1] * K)
    bent = tuple(-1 if (x & 1) and (x >> 1 & 1) else 1 for x in range(K))
    bases = [one, bent]
    frames, psi = [], []
    for _ in range(n_left):
        base = random.choice(bases)
        d = random.randrange(K)
        frames.append(tuple(base[x] * chi(d, x) for x in range(K)))
        p = list(range(K))
        random.shuffle(p)
        psi.append(p)  # psi[u][a] = vector coordinate of label a
    edges = []  # (u, v, pi) with pi[a] = right label
    good = []
    cross = 0
    for v in range(n_right):
        u0 = random.randrange(n_left)
        if random.random() < 0.4:
            # GKOPTW-style coset pairing of <gamma>: never forcing
            gm0 = random.randrange(1, K)
            P = [(c, c ^ gm0) for c in range(K) if c < c ^ gm0]
        else:
            P = random_pairing(K)  # in vector coordinates of u0
        gammas = {a ^ b for a, b in P}
        hs = []
        for g in range(n_left):
            h = tuple(frames[g][x] * frames[u0][x] for x in range(K))
            if all(restricted_linear(h, gm, hps, lin) for gm in gammas):
                hs.append(g)
        nbrs = [u0] + random.sample([g for g in hs if g != u0],
                                    min(max_deg - 1, len(hs) - 1))
        if any(frames[g] not in {tuple(frames[u0][x] * chi(c, x) for x in range(K))
                                 for c in range(K)} for g in nbrs):
            cross += 1
        ys = [pair_sum(frames[u0], a, b, K) for a, b in P]
        for g in nbrs:
            sums = {}
            for a in range(K):
                for b in range(a + 1, K):
                    sums[pair_sum(frames[g], a, b, K)] = (a, b)
            inv = {c: a for a, c in enumerate(psi[g])}
            pi = [None] * K
            for bl, y in enumerate(ys):
                c1, c2 = sums[y]  # KeyError would refute the pair-sum lemma
                pi[inv[c1]] = bl
                pi[inv[c2]] = bl
            assert None not in pi
            # perfect SDP identity y_(v,b) = sum_(a in pi^-1(b)) x_(g,a)
            for bl, y in enumerate(ys):
                s = [0] * K
                for a in range(K):
                    if pi[a] == bl:
                        vec = frame_vec(frames[g], psi[g][a], K)
                        s = [s[i] + vec[i] for i in range(K)]
                assert tuple(s) == y
            edges.append((g, v, pi))
        th = is_two_hitting(diff_mask(P), masks)
        fo = forcing(k, sorted(gammas))
        assert fo or not th
        good.append(fo)
    # components of left vertices joined through good right vertices
    parent = list(range(n_left))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    by_v = {}
    for g, v, pi in edges:
        by_v.setdefault(v, []).append((g, pi))
    for v, lst in by_v.items():
        if good[v]:
            for g, _ in lst[1:]:
                parent[find(g)] = find(lst[0][0])
    w = {}
    label = [None] * n_left
    for u in range(n_left):
        r = find(u)
        if r not in w:
            w[r] = frame_vec(frames[r], 0, K)
        hits = [a for a in range(K) if frame_vec(frames[u], psi[u][a], K) == w[r]]
        if len(hits) == 1:
            label[u] = hits[0]
    right = {}
    sat_good, tot_good, tot = 0, 0, len(edges)
    for v, lst in by_v.items():
        if not good[v]:
            continue
        g0, pi0 = lst[0]
        assert label[g0] is not None, "vector set of a good component not common"
        right[v] = pi0[label[g0]]
        for g, pi in lst:
            tot_good += 1
            assert label[g] is not None
            if pi[label[g]] == right[v]:
                sat_good += 1
    assert sat_good == tot_good
    return tot, tot_good, sat_good, sum(good), cross


def main():
    quick = "--quick" in sys.argv
    n, st = check_A(3, 0, 105, exhaustive=True)
    print("A k=3: %d pairings (all), direct vector test on all; %s" % (n, st))
    n, st = check_A(4, 60 if quick else 400, 4 if quick else 12, exhaustive=False)
    print("A k=4: %d random pairings; %s" % (n, st))
    print("B k=3: brute-force forcing == GF(2) forcing, 2-hitting => forcing; %s"
          % check_B())
    for row in check_C(6 if quick else 7, 4000 if quick else 20000):
        k, K, kind, p, b = row
        print("C k=%d K=%d p_K %s = %s ; analytic bound %.4g" % (k, K, kind, p, b))
    for K in (64, 128, 256, 512, 1024, 2048, 4096):
        print("C bound K=%d: %.4g   (K^2/6)(7/8)^(K/8) = %.4g"
              % (K, analytic_bound(K), K * K / 6 * (7 / 8) ** (K / 8)))
    for k in (3, 4):
        tot, tg, sg, ng, cross = check_D(k, 30, 50, 4)
        print("D k=%d: %d edges, %d at good right vertices, %d satisfied; "
              "%d good right vertices; %d right vertices with non-character "
              "co-neighbour frames" % (k, tot, tg, sg, ng, cross))
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
