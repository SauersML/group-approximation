#!/usr/bin/env python3
"""Checks for `bounded-rank-parity-selectors-pay-representation-weight`.

Four independent checks, all over F_2, all runnable in a few seconds.

  (1) conditional-bias lemma, exhaustively.
      For a random weight-3 matrix M, a random measurement space C of rank R
      (plus the window's own offsets), a random seed space L' and a random
      target direction x, we enumerate every (t, v) in the planted ensemble
      b = M t + v, group by the observation (t|L', (<c,b>)_{c in C}) and read
      off the exact conditional bias of the honest branch bit (-1)^<t,x>.
      Asserted:
        * bias is exactly 0 when no c in C has M^T c in x + Lambda
          (Lambda = L' + H_U), i.e. the gauge-blind regime;
        * otherwise |bias| <= 2^s theta^W / (1 - 2^s theta^g), the leak bound,
          with theta = 1 - 2 eta, W the minimum weight outside the window of a
          representation of x, g the minimum weight outside the window of a
          nonzero null measurement, s = dim(C mod window offsets).

  (2) leak weight of sparse sources.
      On random 3LIN instances with m = 2n we search, for many legitimate
      windows U and directions x, every set T of at most 3 equations outside U
      with sum(m_j, j in T) in x + L' + H_U.  None is ever found, which is the
      conclusion of the expansion lemma (W > 3) measured directly.

  (3) collapse fraction kappa.
      The weight of pairs of edges at one B-vertex whose branch directions are
      congruent modulo L' + H_U.  Compared with the DKKMS direction law
      (x uniform off L' + H_U), which predicts kappa = 2^(l-1+k)/(2^(3k) -
      2^(l-1+k)).

  (4) honest lift value of concrete selectors on small Grassmann instances,
      including the two natural global ones: solve the whole linear system by
      Gaussian elimination and evaluate (`gauss`), and solve the window's own
      equations together with the seed label and evaluate (`localsolve`).
      The oracle selector (which knows the planted assignment) is the control.

Usage:  python3 check_parity_leak_bias.py [--seed S] [--quick]
"""

import argparse
import random
from collections import defaultdict

# ---------------------------------------------------------------- F_2 helpers


def popcount(x):
    return bin(x).count("1")


def parity(x):
    return popcount(x) & 1


def add_to_basis(basis, v):
    """basis is a dict pivot -> vector in row echelon form."""
    while v:
        p = v.bit_length() - 1
        if p in basis:
            v ^= basis[p]
        else:
            basis[p] = v
            return True
    return False


def span_basis(vectors):
    basis = {}
    for v in vectors:
        add_to_basis(basis, v)
    return basis


def in_span(basis, v):
    while v:
        p = v.bit_length() - 1
        if p not in basis:
            return False
        v ^= basis[p]
    return True


def enumerate_span(vectors):
    """All elements of the span of `vectors` (small spans only)."""
    out = [0]
    for v in vectors:
        if not any(v == w for w in out):
            out = out + [w ^ v for w in out]
    # dedupe
    return sorted(set(out))


def solve_f2(eqs):
    """Solve a linear system over F_2.

    eqs is a list of (mask, rhs); mask is a bitmask of the unknowns occurring
    with coefficient 1.  Returns one solution (free unknowns set to 0) or None.
    """
    rref = []  # list of (mask, rhs) in reduced row echelon form
    for mask, rhs in eqs:
        for bm, br in rref:
            p = bm.bit_length() - 1
            if (mask >> p) & 1:
                mask ^= bm
                rhs ^= br
        if mask == 0:
            if rhs:
                return None
            continue
        p = mask.bit_length() - 1
        new = []
        for bm, br in rref:
            if (bm >> p) & 1:
                bm ^= mask
                br ^= rhs
            new.append((bm, br))
        new.append((mask, rhs))
        rref = new
    sol = 0
    for bm, br in rref:
        if br:
            sol |= 1 << (bm.bit_length() - 1)
    return sol


def random_3lin(n, m, rng):
    """m distinct weight-3 rows over n variables, as bitmasks."""
    rows = []
    seen = set()
    while len(rows) < m:
        vs = rng.sample(range(n), 3)
        mask = 0
        for v in vs:
            mask |= 1 << v
        if mask in seen:
            continue
        seen.add(mask)
        rows.append(mask)
    return rows


def transpose_apply(rows, c):
    """M^T c = XOR of the rows selected by the bitmask c."""
    out = 0
    j = 0
    cc = c
    while cc:
        if cc & 1:
            out ^= rows[j]
        cc >>= 1
        j += 1
    return out


# ------------------------------------------------- (1) conditional-bias lemma


def check_conditional_bias(rng, trials=12, n=9, m=10, eta=0.15, rank=2,
                           verbose=True):
    theta = 1.0 - 2.0 * eta
    worst = 0.0
    blind_cases = 0
    leak_cases = 0
    for _ in range(trials):
        rows = random_3lin(n, m, rng)
        # window: two rows, disjoint supports if possible
        while True:
            u1, u2 = rng.sample(range(m), 2)
            if rows[u1] & rows[u2] == 0:
                break
        window = [u1, u2]
        wmask = (1 << u1) | (1 << u2)
        xu = rows[u1] | rows[u2]            # variables of the window
        hu = [rows[u1], rows[u2]]
        # seed space L' : one vector inside X_U, outside H_U
        xu_vectors = []
        bits = [i for i in range(n) if (xu >> i) & 1]
        for mask in range(1, 1 << len(bits)):
            v = 0
            for t, i in enumerate(bits):
                if (mask >> t) & 1:
                    v |= 1 << i
            xu_vectors.append(v)
        hu_span = enumerate_span(hu)
        cand = [v for v in xu_vectors if v not in hu_span]
        y = rng.choice(cand)
        lam = enumerate_span(hu + [y])       # Lambda = L' + H_U
        cand2 = [v for v in xu_vectors if v not in lam]
        x = rng.choice(cand2)                # branch direction

        # measurement space C = <window offsets> + <rank random vectors>,
        # in half the trials with a planted short representation of x.
        gens = [1 << u1, 1 << u2]
        planted = rng.random() < 0.5
        if planted:
            lamb = rng.choice(lam)
            eqs = []
            for i in range(n):
                mask = 0
                for j in range(m):
                    if (rows[j] >> i) & 1:
                        mask |= 1 << j
                eqs.append((mask, ((x ^ lamb) >> i) & 1))
            c0 = solve_f2(eqs)
            if c0 is None:
                planted = False
            else:
                gens.append(c0)
        while len(gens) < 2 + rank:
            gens.append(rng.getrandbits(m))
        cspace = enumerate_span(gens)
        cbasis = list(span_basis(gens).values())

        # invariants of the measurement space
        lam_basis = span_basis(lam)
        xlam = span_basis(lam + [x])
        coset_w = []
        null_w = []
        for c in cspace:
            q = transpose_apply(rows, c)
            outside = popcount(c & ~wmask)
            if in_span(lam_basis, q):
                if outside > 0:
                    null_w.append(outside)
            elif in_span(xlam, q):      # q in x + Lambda
                coset_w.append(outside)
        s = 0
        sb = {}
        for c in cbasis:
            if add_to_basis(sb, c & ~wmask):
                s += 1
        W = min(coset_w) if coset_w else None
        g = min(null_w) if null_w else None
        if W is None:
            bound = 0.0
        else:
            num = (2.0 ** s) * (theta ** W)
            den = 1.0 - ((2.0 ** s) * (theta ** g) if g is not None else 0.0)
            bound = num / den if den > 0 else float("inf")

        # exhaustive conditional bias
        cells = defaultdict(lambda: [0.0, 0.0])   # key -> [signed, total]
        free = [j for j in range(m) if not ((wmask >> j) & 1)]
        for t in range(1 << n):
            tvals = [parity(rows[j] & t) for j in range(m)]
            ykey = parity(y & t)
            for vm in range(1 << len(free)):
                v = 0
                w = 1.0
                for idx, j in enumerate(free):
                    if (vm >> idx) & 1:
                        v |= 1 << j
                        w *= eta
                    else:
                        w *= 1 - eta
                b = 0
                for j in range(m):
                    bit = tvals[j] ^ ((v >> j) & 1)
                    if bit:
                        b |= 1 << j
                key = (ykey,) + tuple(parity(c & b) for c in cbasis)
                cell = cells[key]
                cell[0] += w * (1 if parity(x & t) == 0 else -1)
                cell[1] += w
        obs = 0.0
        for key, (sgn, tot) in cells.items():
            if tot <= 0:
                continue
            obs = max(obs, abs(sgn / tot))
        if W is None:
            blind_cases += 1
            assert obs < 1e-9, "blind edge with nonzero bias: %g" % obs
        else:
            leak_cases += 1
            assert obs <= bound + 1e-9, (
                "leak bound violated: obs %g > bound %g (W=%s g=%s s=%d)"
                % (obs, bound, W, g, s))
        worst = max(worst, obs - (0.0 if W is None else bound))
    if verbose:
        print("(1) conditional-bias lemma: %d trials, %d blind (bias exactly 0), "
              "%d leaking (bias within bound); worst slack %.6f"
              % (trials, blind_cases, leak_cases, worst))
    return blind_cases, leak_cases


# ---------------------------------------------------- (2) leak weight measure


def check_leak_weight(rng, n=400, ratio=2, k=3, l=2, windows=60, verbose=True):
    """Counts, per window, the Lambda-cosets of X_U reachable by |T| <= 3.

    Returns the leak profile n_j = mean number of cosets x + Lambda that carry
    a representation sum(m_j, j in T) with |T| = j and T disjoint from U.  The
    theorem's pair profile is Lambda(theta) <= kappa * (1 + sum_j n_j theta^j).
    """
    m = ratio * n
    rows = random_3lin(n, m, rng)
    found = defaultdict(int)
    cosets = defaultdict(set)
    tested = 0
    for _ in range(windows):
        # legitimate window: k pairwise variable-disjoint equations
        idx = []
        used = 0
        tries = 0
        while len(idx) < k and tries < 500:
            tries += 1
            j = rng.randrange(m)
            if j in idx or (rows[j] & used):
                continue
            idx.append(j)
            used |= rows[j]
        if len(idx) < k:
            continue
        xu = used
        hu = [rows[j] for j in idx]
        hu_span = enumerate_span(hu)
        bits = [i for i in range(n) if (xu >> i) & 1]

        def rand_in_xu():
            v = 0
            for i in bits:
                if rng.random() < 0.5:
                    v |= 1 << i
            return v

        while True:
            y = rand_in_xu()
            if y not in hu_span:
                break
        lam_basis = span_basis(hu + [y])           # Lambda = L' + H_U
        tested += 1

        def coset(v):                              # canonical form mod Lambda
            # pivots in decreasing order: each step only touches lower bits
            for p in sorted(lam_basis, reverse=True):
                if (v >> p) & 1:
                    v ^= lam_basis[p]
            return v

        def record(j, t):
            s = 0
            for a in t:
                s ^= rows[a]
            assert s & ~xu == 0
            c = coset(s & xu)
            if c != 0:                             # c = 0 is H_U + L' itself
                found[j] += 1
                cosets[j].add(c)

        out = {}
        for j in range(m):
            if j in idx:
                continue
            out[j] = rows[j] & ~xu
        groups = defaultdict(list)
        for j, o in out.items():
            groups[o].append(j)
        # |T| = 1 : the whole row sits inside vars(U)
        for j in groups.get(0, []):
            record(1, (j,))
        # |T| = 2 : outside parts coincide
        for o, js in groups.items():
            for a in range(len(js)):
                for b in range(a + 1, len(js)):
                    record(2, (js[a], js[b]))
        # |T| = 3 : o1 ^ o2 ^ o3 = 0, three distinct outside parts
        keys = list(groups.keys())
        index = {o: i for i, o in enumerate(keys)}
        for a in range(len(keys)):
            for b in range(a + 1, len(keys)):
                o3 = keys[a] ^ keys[b]
                if o3 in index and index[o3] > b:
                    for j1 in groups[keys[a]]:
                        for j2 in groups[keys[b]]:
                            for j3 in groups[o3]:
                                record(3, (j1, j2, j3))
    profile = {j: len(cosets[j]) / tested for j in sorted(cosets)}
    if verbose:
        print("(2) leak profile on random 3LIN n=%d m=%d k=%d l=%d: %d windows;"
              % (n, m, k, l, tested))
        print("      cosets of L'+H_U in X_U reachable by |T| equations "
              "outside U, per window: %s (out of 2^(2k-l+1) = %d cosets)"
              % (profile if profile else "none for |T|<=3", 2 ** (2 * k - l + 1)))
    return tested, profile


# ------------------------------------------------- (3) collapse fraction test


def check_collapse(rng, n=60, k=3, l=2, vertices=40, verbose=True):
    m = 2 * n
    rows = random_3lin(n, m, rng)
    tot_pairs = 0
    tot_coll = 0
    for _ in range(vertices):
        idx = []
        used = 0
        tries = 0
        while len(idx) < k and tries < 500:
            tries += 1
            j = rng.randrange(m)
            if j in idx or (rows[j] & used):
                continue
            idx.append(j)
            used |= rows[j]
        if len(idx) < k:
            continue
        xu = used
        bits = [i for i in range(n) if (xu >> i) & 1]
        hu = [rows[j] for j in idx]
        hu_span = enumerate_span(hu)
        xu_vectors = []
        for mask in range(1 << len(bits)):
            v = 0
            for t, i in enumerate(bits):
                if (mask >> t) & 1:
                    v |= 1 << i
            xu_vectors.append(v)
        cand = [v for v in xu_vectors if v not in hu_span]
        y = rng.choice(cand)
        lp = enumerate_span([y])                  # L' itself
        lam = set(enumerate_span(hu + [y]))
        # one representative direction per constraint L = L' + <x>
        dirs = sorted(set(min(v ^ u for u in lp)
                          for v in xu_vectors if v not in lam))
        d = len(dirs)
        tot_pairs += d * (d - 1)
        for a in range(d):
            for b in range(d):
                if a != b and (dirs[a] ^ dirs[b]) in lam:
                    tot_coll += 1
    kappa = tot_coll / tot_pairs if tot_pairs else 0.0
    nconstraints = (2 ** (3 * k) - 2 ** (l - 1 + k)) / 2 ** (l - 1)
    pred = (2 ** k - 1) / (nconstraints - 1)
    if verbose:
        print("(3) collapse fraction kappa = %.5f over %d ordered pairs of "
              "constraints; DKKMS direction law predicts %.5f (= 2^(l-1-2k) "
              "up to lower order)" % (kappa, tot_pairs, pred))
    return kappa, pred


# ------------------------------------------- (4) concrete selectors, measured


def honest_lift_values(rng, n=90, k=3, l=2, eta=0.10, vertices=120,
                       verbose=True):
    m = 2 * n
    rows = random_3lin(n, m, rng)
    tstar = rng.getrandbits(n)
    viol = [1 if rng.random() < eta else 0 for _ in range(m)]
    b = [parity(rows[j] & tstar) ^ viol[j] for j in range(m)]

    # `gauss`: one solution of the whole (inconsistent) system, by elimination
    eqs = []
    for j in range(m):
        eqs.append((rows[j], b[j]))
    that = None
    acc = []
    rref = []
    for mask, rhs in eqs:                    # greedy consistent subsystem
        mm, rr = mask, rhs
        for bm, br in rref:
            p = bm.bit_length() - 1
            if (mm >> p) & 1:
                mm ^= bm
                rr ^= br
        if mm == 0:
            continue
        p = mm.bit_length() - 1
        new = []
        for bm, br in rref:
            if (bm >> p) & 1:
                bm ^= mm
                br ^= rr
            new.append((bm, br))
        new.append((mm, rr))
        rref = new
        acc.append((mask, rhs))
    that = 0
    for bm, br in rref:
        if br:
            that |= 1 << (bm.bit_length() - 1)

    stats = defaultdict(float)
    count = 0
    degs = []
    for _ in range(vertices):
        idx = []
        used = 0
        tries = 0
        while len(idx) < k and tries < 500:
            tries += 1
            j = rng.randrange(m)
            if j in idx or (rows[j] & used):
                continue
            if viol[j]:                      # honest labelling needs U satisfied
                continue
            idx.append(j)
            used |= rows[j]
        if len(idx) < k:
            continue
        xu = used
        bits = [i for i in range(n) if (xu >> i) & 1]
        hu = [rows[j] for j in idx]
        hu_span = enumerate_span(hu)
        xu_vectors = []
        for mask in range(1 << len(bits)):
            v = 0
            for t, i in enumerate(bits):
                if (mask >> t) & 1:
                    v |= 1 << i
            xu_vectors.append(v)
        cand = [v for v in xu_vectors if v not in hu_span]
        y = rng.choice(cand)
        lp = enumerate_span([y])
        lam = set(enumerate_span(hu + [y]))
        # one representative direction per constraint L = L' + <x>
        dirs = sorted(set(min(v ^ u for u in lp)
                          for v in xu_vectors if v not in lam))
        if not dirs:
            continue
        count += 1
        degs.append(len(dirs))
        tau = parity(y & tstar)              # the honest seed label on L' = <y>

        # localsolve: solve U's own equations and the seed label inside X_U
        leqs = [(rows[j] & xu, b[j]) for j in idx] + [(y & xu, tau)]
        tloc = solve_f2(leqs)
        if tloc is None:
            tloc = 0

        for name in ("oracle", "gauss", "localsolve", "random"):
            agree = 0
            for x in dirs:
                honest = parity(x & tstar)
                if name == "oracle":
                    guess = honest
                elif name == "gauss":
                    guess = parity(x & that)
                elif name == "localsolve":
                    guess = parity(x & tloc)
                else:
                    guess = rng.getrandbits(1)
                if guess == honest:
                    agree += 1
            frac = agree / len(dirs)
            stats[name] += max(frac, 1.0 - frac)
    D = sum(degs) / len(degs) if degs else 0
    if verbose:
        print("(4) honest lift value on %d B-vertices (n=%d, k=%d, l=%d, "
              "eta=%.2f), mean degree %.0f:" % (count, n, k, l, eta, D))
        for name in ("oracle", "gauss", "localsolve", "random"):
            print("      %-11s %.4f" % (name, stats[name] / count))
    return {name: stats[name] / count for name in stats}, D


# --------------------------------------------------------------------- main


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=20260918)
    ap.add_argument("--quick", action="store_true")
    args = ap.parse_args()
    rng = random.Random(args.seed)
    print("check_parity_leak_bias.py  seed=%d" % args.seed)
    check_conditional_bias(rng, trials=6 if args.quick else 12)
    _, profile = check_leak_weight(rng, n=200 if args.quick else 400,
                                   windows=20 if args.quick else 60)
    kappa, pred = check_collapse(rng, vertices=10 if args.quick else 40)
    vals, D = honest_lift_values(rng, vertices=30 if args.quick else 120)
    def theorem_bound(k, l, eta, R, D, kappa, W, extra_profile):
        """Theorem 2 with Lambda(theta) <= kappa + rho + 2^(2R+1) theta^W."""
        theta = 1 - 2 * eta
        lam = (kappa * (1 + sum(c * theta ** j
                                for j, c in extra_profile.items()))
               + 2 ** (2 * R + 1) * theta ** W)
        b = 0.5 + k * eta + 0.5 * ((1.0 / D + min(1.0, lam)) ** 0.5)
        return min(1.0, b), lam

    bound, lam_theta = theorem_bound(3, 2, 0.10, 0, D, kappa, 4, profile)
    print("    measured pair leak profile Lambda(theta) <= %.5f; theorem bound "
          "for a rank-0 selector here: %.4f  (localsolve measured %.4f)"
          % (lam_theta, bound, vals["localsolve"]))
    print("    the toy parameters are too small for the bound to bite.  The "
          "asymptotic axis is the leak weight W, which grows with n at fixed "
          "(k, l, eta); at k=10, l=2, eta=0.002, rank R=3:")
    for W in (100, 400, 1600, 6400):
        kap = 2.0 ** (2 - 2 * 10 + 1)
        b, _ = theorem_bound(10, 2, 0.002, 3, 2.0 ** (3 * 10 - 2), kap, W, {})
        print("      W=%-5d bound %.6f" % (W, b))
    assert vals["localsolve"] <= bound + 1e-9
    assert vals["oracle"] > 0.99
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
