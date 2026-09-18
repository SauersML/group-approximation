#!/usr/bin/env python3
"""Checks for local-witnesses-of-dkkms-2to1-instances-are-sound-on-planted-inputs.

Part 1 (exact coupling). On a toy DKKMS-shaped folded 2-to-1 game built from a
3LIN matrix H with a NO right-hand side b0, for random *local* labelling rules
(class labels read only (U, class, b_U); B labels read only (V, L', b on V's
full equations)), it computes E_t val on the planted YES inputs (H, Ht) and on
the NO coset (H, b0 + Ht) by exhaustive enumeration of t, and checks equality
as exact fractions. Controls: a global rule (solve Hx = b) breaks equality, and
b_S is exactly uniform for independent row sets S, but not for dependent ones.

Part 2 (share). Samples the DKKMS test process and computes, for each sampled
A-vertex (U, L), the posterior w(R | U, L) over hyperplanes R of L of being the
B-side subspace L', via the per-equation generating function, and reports
share = E_L max_R w(R | U, L). This is the value of the trivial local witness
(B = 0, class labels killing the dominant seed) up to class-conflict loss.

Usage: python3 check_local_witness_coupling.py [--seed S] [--samples N]
"""
import argparse
import itertools
import random
from fractions import Fraction


# ---------- GF(2) linear algebra on int bitmasks ----------

def span(basis):
    out = {0}
    for v in basis:
        out |= {x ^ v for x in out}
    return out


def reduce_basis(vecs):
    """Return an echelon basis (list) of the span of vecs."""
    basis = []
    for v in vecs:
        for b in basis:
            v = min(v, v ^ b)
        if v:
            basis.append(v)
            basis.sort(reverse=True)
    return basis


def rank(vecs):
    return len(reduce_basis(vecs))


def subspaces_of_dim(ambient_basis, d):
    """All d-dim subspaces of span(ambient_basis), as frozensets of vectors."""
    vecs = sorted(span(ambient_basis) - {0})
    seen = set()
    out = []
    for combo in itertools.combinations(vecs, d):
        if rank(list(combo)) != d:
            continue
        s = frozenset(span(list(combo)))
        if s not in seen:
            seen.add(s)
            out.append(s)
    return out


def gauss_binom(n, k):
    if k < 0 or k > n:
        return 0
    num = den = 1
    for i in range(k):
        num *= (1 << (n - i)) - 1
        den *= (1 << (i + 1)) - 1
    return num // den


def parity(x):
    return bin(x).count("1") & 1


# ---------- Part 1: toy DKKMS-shaped folded game ----------

def random_3lin(n, m, rng):
    rows = []
    while len(rows) < m:
        r = sum(1 << v for v in rng.sample(range(n), 3))
        if r not in rows:
            rows.append(r)
    return rows


def rhs_of(rows, t):
    return tuple(parity(r & t) for r in rows)


def find_no_rhs(rows, n):
    image = {rhs_of(rows, t) for t in range(1 << n)}
    for bits in itertools.product((0, 1), repeat=len(rows)):
        if bits not in image:
            return bits, image
    return None, image


def sample_edges(rows, n, k, l, beta, num_edges, rng):
    """Sample edges (U, V, L', L) from the DKKMS-shaped process (k tuples of
    pairwise variable-disjoint rows, V keeps each row w.p. 1-beta else one of
    its variables, L' uniform in Gr(X_V, l-1), L uniform among l-spaces of X_U
    containing L' with L meet H_U = 0)."""
    m = len(rows)
    tuples = [U for U in itertools.combinations(range(m), k)
              if all(rows[a] & rows[b] == 0 for a, b in itertools.combinations(U, 2))]
    cache_gr = {}
    edges = []
    while len(edges) < num_edges:
        U = rng.choice(tuples)
        HU = [rows[e] for e in U]
        HUspan = span(HU)
        full, singles = [], []
        for e in U:
            if rng.random() < 1 - beta:
                full.append(e)
            else:
                vs = [v for v in range(n) if rows[e] >> v & 1]
                singles.append(rng.choice(vs))
        XV = [1 << v for e in full for v in range(n) if rows[e] >> v & 1] + [1 << v for v in singles]
        XU = [1 << v for e in U for v in range(n) if rows[e] >> v & 1]
        key = tuple(sorted(XV))
        if (key, l - 1) not in cache_gr:
            cache_gr[(key, l - 1)] = subspaces_of_dim(XV, l - 1)
        Lp = rng.choice(cache_gr[(key, l - 1)])
        keyU = tuple(sorted(XU))
        if (keyU, l) not in cache_gr:
            cache_gr[(keyU, l)] = subspaces_of_dim(XU, l)
        cands = [L for L in cache_gr[(keyU, l)] if Lp <= L and not (L & HUspan) - {0}]
        if not cands:
            continue
        L = rng.choice(cands)
        edges.append((U, tuple(sorted(full)), tuple(sorted(singles)), Lp, L))
    return edges


def class_data(rows, U, L):
    """Folding class W = L + H_U, canonical complement basis c of H_U in W, and
    a map vector -> (coefficients on H_U rows, coefficients on c)."""
    HU = [rows[e] for e in U]
    W = frozenset(span(list(L) + HU))
    comp = []
    for v in sorted(W):
        if rank(HU + comp + [v]) > len(HU) + len(comp):
            comp.append(v)
    coords = {}
    for a in itertools.product((0, 1), repeat=len(HU)):
        for d in itertools.product((0, 1), repeat=len(comp)):
            v = 0
            for ai, h in zip(a, HU):
                if ai:
                    v ^= h
            for di, c in zip(d, comp):
                if di:
                    v ^= c
            coords[v] = (a, d)
    return W, comp, coords


def prepare(rows, edges):
    prep = []
    cls_cache = {}
    for (U, full, singles, Lp, L) in edges:
        ck = (U, frozenset(span(list(L) + [rows[e] for e in U])))
        if ck not in cls_cache:
            cls_cache[ck] = class_data(rows, U, L)
        W, comp, coords = cls_cache[ck]
        ybasis = reduce_basis(list(Lp))
        prep.append((U, W, full, singles, frozenset(Lp), ybasis, [coords[y] for y in ybasis]))
    return prep


class LocalRule:
    """Random local rule: class bits read (U, W, b_U); B bits read (V, L', b_full(V)).
    Optional extra rows per U (a larger read set S_U) for the extension check."""

    def __init__(self, seed, extra=None):
        self.rng = random.Random(seed)
        self.tabA, self.tabB = {}, {}
        self.extra = extra or {}

    def a_bits(self, U, W, b, ncomp):
        key = (U, W, tuple(b[e] for e in U), tuple(b[e] for e in self.extra.get(U, ())))
        if key not in self.tabA:
            self.tabA[key] = tuple(self.rng.randrange(2) for _ in range(ncomp))
        return self.tabA[key]

    def b_bits(self, full, singles, Lp, b, dim):
        key = (full, singles, Lp, tuple(b[e] for e in full))
        if key not in self.tabB:
            self.tabB[key] = tuple(self.rng.randrange(2) for _ in range(dim))
        return self.tabB[key]


def edge_accepts(pe, b, rule):
    U, W, full, singles, Lp, ybasis, ycoords = pe
    bits = rule.a_bits(U, W, b, len(ycoords[0][1]))
    bb = rule.b_bits(full, singles, Lp, b, len(ybasis))
    for (a, d), want in zip(ycoords, bb):
        val = 0
        for ai, e in zip(a, U):
            val ^= ai & b[e]
        for di, x in zip(d, bits):
            val ^= di & x
        if val != want:
            return False
    return True


def per_edge_rates(prep, rows, n, rule, offset):
    counts = [0] * len(prep)
    for t in range(1 << n):
        b = tuple(o ^ parity(r & t) for o, r in zip(offset, rows))
        for i, pe in enumerate(prep):
            if rule(pe, b):
                counts[i] += 1
    return counts


def part1(seed, n=9, m=12, k=2, l=2, beta=0.5, num_edges=600, num_rules=4):
    rng = random.Random(seed)
    rows = random_3lin(n, m, rng)
    b0, image = find_no_rhs(rows, n)
    assert b0 is not None, "H has full row rank; no NO right-hand side"
    zero = (0,) * m
    print(f"Part 1: n={n} m={m} rank(H)={rank(rows)} k={k} l={l} beta={beta}; b0 is NO: {b0 not in image}")

    # (a) b_S exactly uniform for independent S, both cases; not for dependent S.
    tuples = [U for U in itertools.combinations(range(m), k)
              if all(rows[a] & rows[b] == 0 for a, b in itertools.combinations(U, 2))]
    bad = 0
    for U in tuples:
        for off in (zero, b0):
            cnt = {}
            for t in range(1 << n):
                key = tuple(off[e] ^ parity(rows[e] & t) for e in U)
                cnt[key] = cnt.get(key, 0) + 1
            if len(cnt) != 1 << k or len(set(cnt.values())) != 1:
                bad += 1
    dep = next(S for s in range(2, m + 1) for S in itertools.combinations(range(m), s)
               if rank([rows[e] for e in S]) < s)
    supp = {tuple(parity(rows[e] & t) for e in dep) for t in range(1 << n)}
    print(f"  (a) legitimate tuples: {len(tuples)}; non-uniform b_U laws: {bad}; "
          f"dependent set {dep}: YES support {len(supp)} of {1 << len(dep)} (control, not uniform)")

    edges = sample_edges(rows, n, k, l, beta, num_edges, rng)
    prep = prepare(rows, edges)
    E = len(prep)

    # (b) random local rules: per-edge acceptance rates equal on YES and NO coset.
    for j in range(num_rules):
        rule = LocalRule(seed * 100 + j)
        f = lambda pe, b: edge_accepts(pe, b, rule)
        yes = per_edge_rates(prep, rows, n, f, zero)
        no = per_edge_rates(prep, rows, n, f, b0)
        vy = Fraction(sum(yes), E << n)
        vn = Fraction(sum(no), E << n)
        mism = sum(1 for a, c in zip(yes, no) if a != c)
        print(f"  (b) local rule {j}: E_t val YES = {vy} = {float(vy):.4f}, NO coset = {vn}; "
              f"equal: {vy == vn}; per-edge mismatches: {mism}/{E}")

    # (c) global control: honest labelling from the least solution of Hx = b.
    sol = {}
    for t in range(1 << n):
        sol.setdefault(rhs_of(rows, t), t)

    def honest(pe, b):
        x = sol.get(b)
        if x is None:
            return edge_accepts(pe, b, zero_rule)
        return True  # the honest labelling of a satisfying x accepts every edge

    zero_rule = LocalRule(0)
    zero_rule.a_bits = lambda U, W, b, nc: (0,) * nc
    zero_rule.b_bits = lambda full, singles, Lp, b, d: (0,) * d
    yes = per_edge_rates(prep, rows, n, honest, zero)
    no = per_edge_rates(prep, rows, n, honest, b0)
    print(f"  (c) global control (solve Hx=b): YES {Fraction(sum(yes), E << n)}, "
          f"NO coset {float(Fraction(sum(no), E << n)):.4f} (must differ)")

    # (d) extension: class rule also reads one neighbouring row r of U.
    extra = {}
    for U in tuples:
        vU = 0
        for e in U:
            vU |= rows[e]
        nb = [r for r in range(m) if r not in U and rows[r] & vU]
        extra[U] = (rng.choice(nb),) if nb else ()
    rule = LocalRule(seed * 100 + 99, extra)
    f = lambda pe, b: edge_accepts(pe, b, rule)
    yes = per_edge_rates(prep, rows, n, f, zero)
    no = per_edge_rates(prep, rows, n, f, b0)
    ind = [rank([rows[e] for e in pe[0] + extra[pe[0]]]) == len(pe[0]) + len(extra[pe[0]]) for pe in prep]
    mi = sum(1 for a, c, i in zip(yes, no, ind) if i and a != c)
    md = sum(1 for a, c, i in zip(yes, no, ind) if not i and a != c)
    print(f"  (d) read set U+neighbour: independent edges {sum(ind)} with {mi} mismatches; "
          f"dependent edges {E - sum(ind)} with {md} mismatches")

    # (e) invariant: every class rule also reads the dependent set dep. Equality
    # must hold for a NO offset that is locally satisfiable on dep, and may fail
    # for one that is locally unsatisfiable on dep.
    dep_extra = {U: tuple(e for e in dep if e not in U) for U in tuples}
    sat_off = next(bits for bits in itertools.product((0, 1), repeat=m)
                   if bits not in image and tuple(bits[e] for e in dep) in supp)
    uns_off = next(bits for bits in itertools.product((0, 1), repeat=m)
                   if bits not in image and tuple(bits[e] for e in dep) not in supp)
    ok_e = True
    for name, off in (("locally satisfiable", sat_off), ("locally refuting", uns_off)):
        rule = LocalRule(seed * 100 + 77, dep_extra)
        f = lambda pe, b: edge_accepts(pe, b, rule)
        yes = per_edge_rates(prep, rows, n, f, zero)
        no = per_edge_rates(prep, rows, n, f, off)
        mism = sum(1 for a, c in zip(yes, no) if a != c)
        print(f"  (e) reads dep, NO offset {name} on dep: per-edge mismatches {mism}/{E}")
        if name == "locally satisfiable" and mism:
            ok_e = False
    return bad == 0 and mi == 0 and ok_e


# ---------- Part 2: seed posterior and share(l, k, beta) ----------

def rand_indep(pool_basis, d, rng, start=()):
    """Uniform random d-tuple extension of start inside span(pool_basis)."""
    out = list(start)
    while len(out) < len(start) + d:
        v = 0
        for p in pool_basis:
            if rng.randrange(2):
                v ^= p
        if v and rank(out + [v]) == len(out) + 1:
            out.append(v)
    return out


def seed_weight(Rvecs, k, l, beta):
    poly = [1.0]
    for i in range(k):
        blk = {(v >> (3 * i)) & 7 for v in Rvecs}
        if blk == {0}:
            a = 3
        elif len(blk) == 2 and (max(blk) in (1, 2, 4)):
            a = 1
        else:
            a = 0
        c0, c1 = 1 - beta, beta * a / 3
        new = [0.0] * (len(poly) + 1)
        for r, p in enumerate(poly):
            new[r] += p * c0
            new[r + 1] += p * c1
        poly = new
    return sum(p / gauss_binom(3 * k - 2 * r, l - 1) for r, p in enumerate(poly)
               if gauss_binom(3 * k - 2 * r, l - 1) > 0)


def share(k, l, beta, samples, rng):
    HU = span([7 << (3 * i) for i in range(k)])
    XU = [1 << j for j in range(3 * k)]
    tot = hit = 0.0
    for _ in range(samples):
        while True:
            XV = []
            for i in range(k):
                if rng.random() < 1 - beta:
                    XV += [1 << (3 * i + j) for j in range(3)]
                else:
                    XV.append(1 << (3 * i + rng.randrange(3)))
            if len(XV) < l - 1:
                continue
            Lp = rand_indep(XV, l - 1, rng)
            Lb = rand_indep(XU, 1, rng, Lp)
            Lset = span(Lb)
            if not (Lset & HU) - {0}:
                break
        true_R = frozenset(span(Lp))
        ws = {}
        for f in range(1, 1 << l):
            R = frozenset(_combo(Lb, c) for c in range(1 << l) if bin(c & f).count("1") % 2 == 0)
            ws[R] = seed_weight(R, k, l, beta)
        Z = sum(ws.values())
        best = max(ws, key=ws.get)
        tot += ws[best] / Z
        hit += best == true_R
    return tot / samples, hit / samples


def _combo(basis, c):
    v = 0
    for j, b in enumerate(basis):
        if (c >> j) & 1:
            v ^= b
    return v


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=20260918)
    ap.add_argument("--samples", type=int, default=1500)
    args = ap.parse_args()
    ok = part1(args.seed)
    print("Part 2: share = E_L max_R w(R | U, L); hit = Pr[argmax is the true L']")
    rng = random.Random(args.seed + 1)
    for (l, beta) in ((3, 0.5), (3, 0.25), (4, 0.5)):
        line = []
        for k in (2, 4, 6, 8):
            s, h = share(k, l, beta, args.samples, rng)
            line.append(f"k={k}: share {s:.3f} hit {h:.3f}")
        print(f"  l={l} beta={beta}: " + "; ".join(line))
    print("PART 1 EXACT CHECKS PASS" if ok else "PART 1 FAILURE")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
