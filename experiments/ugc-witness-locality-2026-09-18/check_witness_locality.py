#!/usr/bin/env python3
"""Witness locality below the cycle scale is gauge blind.

Claim under test: `lift-witness-rules-below-cycle-scale-are-gauge-blind`.

Setting.  A 3LIN source is a matrix `M` in F_2^(m x n) with rows of weight 3 and a
right-hand side `b` in F_2^m.  The gauge acts by `b -> b + M z`, so the satisfiable
instances over `M` are exactly the coset `Im(M)`, and every coset of `Im(M)` is a
gauge orbit of constant 3LIN value.  The **cycle code** is

    C_perp = ker(M^T) = { c in F_2^m : sum_{j in supp(c)} m_j = 0 },

and the **cycle scale** `d_cyc(M)` is its minimum nonzero weight.  A set `S` of
equations is *cycle free* iff the rows `(m_j)_{j in S}` are independent, and every
set of size `< d_cyc` is cycle free.

The abstract lift reproduces the only structural facts the proof uses about the
folded DKKMS orientation lift, imported verbatim in the claim file:

  * vertices, subspaces, branch vectors and weights depend on `M` only;
  * `b` enters only through the folding offsets `h_U(x_j) = b_j`, so the
    constraint of an edge depends on `b` through the equations of the two
    windows it joins;
  * a view-local selector's orientation depends on `b` through its view `J_e`.

Concretely, an A-vertex `a` carries a window equation `j_a`, a B-vertex `v` a
window equation `j_v`; the A-labels are F_2^2 and the B-labels F_2^1; an edge
`e = (a, v)` accepts `(sigma, tau)` iff

    sigma_0 + delta_e(b) = tau        (folded agreement, offset local to T_e)
    sigma_1 + c_e(b)     = g_e(b|J_e)(tau)   (branch bit chosen by the selector)

with `T_e = {j_a, j_v}`, `J_e = T_e`, and `delta_e`, `c_e` linear in `b|T_e`.

A **witness rule** assigns a label to each vertex as a function of `b`.  It is
`R`-local when each vertex's label depends on at most `R` coordinates of `b`.
The three rules tested are

  * `zero`   : sigma_a = 0 -- the folded zero label, which unfolds to the DKKMS
               gauge labelling `F*` of `grassmann-composed-2to2-coarsenings-are-satisfiable`;
  * `greedy` : sigma_a maximises the number of edges at `a` whose branch bit is
               right when the B-side is assumed consistent -- the per-A-vertex
               local maximiser, i.e. the decoupled upper bound of the route file;
  * `random` : an arbitrary fixed function of `b` on the vertex neighbourhood.

In each case the B-label is read off the designated first edge at the B-vertex.

What is checked (`--mode main`):

  1. every edge's dependency set `S_e` is cycle free;
  2. the exact average lift value of each rule is *identical* on every coset of
     `Im(M)`, i.e. identical on the satisfiable gauge orbit and on every
     unsatisfiable one -- the theorem;
  3. the greedy rule does beat one half, so the equality is not vacuous;
  4. control: a rule that reads a cycle (one parity of the cycle code, a
     non-local rule of support `d_cyc`) separates the cosets, so the cycle scale
     is the exact threshold;
  5. control: after duplicating an equation, which creates a weight-2 cycle, a
     2-local rule that reads both copies separates the cosets.

`--mode decouple` checks on tiny instances that
`val(U_o) <= sum_a max_sigma (branch score at a)` and that this decoupled bound
is vacuous for the selector `g_e(view)(tau) := c_e(b)`, which makes the branch
bit correct for `sigma = 0` at every edge at once.

Run: `python3 check_witness_locality.py`
"""

from __future__ import annotations

import argparse
import itertools
import random
from fractions import Fraction

# --------------------------------------------------------------------------
# linear algebra over F_2, vectors as python ints (bitmasks)
# --------------------------------------------------------------------------


def rank(vectors):
    basis = []
    for v in vectors:
        for bvec in basis:
            v = min(v, v ^ bvec)
        if v:
            basis.append(v)
            basis.sort(reverse=True)
    return len(basis)


def kernel_basis(rows, ncols):
    """Basis of { x in F_2^ncols : rows . x = 0 }, rows given as bitmasks."""
    pivots = {}
    reduced = []
    for r in rows:
        cur = r
        for p, pr in pivots.items():
            if (cur >> p) & 1:
                cur ^= pr
        if cur:
            p = cur.bit_length() - 1
            pivots[p] = cur
            reduced.append(cur)
    free = [c for c in range(ncols) if c not in pivots]
    basis = []
    for f in free:
        x = 1 << f
        # back substitute
        for p in sorted(pivots):
            pr = pivots[p]
            # coefficient of pivot p is the parity of pr . x restricted to free part
            if bin(pr & x).count("1") % 2 == 1:
                x ^= 1 << p
        basis.append(x)
    # sanity
    for x in basis:
        for r in rows:
            assert bin(r & x).count("1") % 2 == 0
    return basis


def span(basis):
    out = [0]
    for b in basis:
        out += [x ^ b for x in out]
    return out


# --------------------------------------------------------------------------
# source
# --------------------------------------------------------------------------


class Source:
    def __init__(self, n, m, rng):
        self.n = n
        self.m = m
        self.rows = []
        seen = set()
        if m > n * (n - 1) * (n - 2) // 12:
            raise ValueError("density too high for distinct weight-3 rows")
        while len(self.rows) < m:
            trip = tuple(sorted(rng.sample(range(n), 3)))
            if trip in seen:
                continue
            seen.add(trip)
            self.rows.append(sum(1 << i for i in trip))
        # cycle code: c in F_2^m with sum_{j in c} rows[j] = 0
        # as a linear system: for every variable i, sum_j c_j * rows[j][i] = 0
        checks = []
        for i in range(n):
            checks.append(sum(1 << j for j in range(m) if (self.rows[j] >> i) & 1))
        self.cycle_basis = kernel_basis(checks, m)
        if len(self.cycle_basis) <= 20:
            words = [w for w in span(self.cycle_basis) if w]
            self.d_cyc = min(bin(w).count("1") for w in words) if words else m + 1
            self.cycle_words = words
        else:
            # too many cycles to enumerate; the exact runs never need them
            self.d_cyc = None
            self.cycle_words = None
        # Im(M) coset representatives: F_2^m / Im(M) is dual to the cycle code,
        # so a transversal is indexed by the syndromes <c, b>, c in cycle code.
        self.rank_M = rank(self.rows)

    def cycle_free(self, idx_set):
        return rank([self.rows[j] for j in idx_set]) == len(idx_set)

    def syndrome(self, b):
        return tuple(bin(w & b).count("1") % 2 for w in self.cycle_basis)

    def coset_reps(self):
        """One representative per coset of Im(M), found by search over low weight."""
        reps = {}
        target = 1 << len(self.cycle_basis)
        for wt in range(0, self.m + 1):
            for sup in itertools.combinations(range(self.m), wt):
                b = sum(1 << j for j in sup)
                s = self.syndrome(b)
                if s not in reps:
                    reps[s] = b
                    if len(reps) == target:
                        return [reps[k] for k in sorted(reps)]
        raise RuntimeError("transversal not found")

    def gauge(self, b, z):
        """b + M z."""
        out = b
        for j in range(self.m):
            if bin(self.rows[j] & z).count("1") % 2 == 1:
                out ^= 1 << j
        return out

    def value(self, b):
        """max fraction of equations satisfiable (brute force over assignments)."""
        best = 0
        for t in range(1 << self.n):
            ok = 0
            for j in range(self.m):
                if bin(self.rows[j] & t).count("1") % 2 == ((b >> j) & 1):
                    ok += 1
            best = max(best, ok)
        return Fraction(best, self.m)


# --------------------------------------------------------------------------
# the abstract folded lift
# --------------------------------------------------------------------------


class Lift:
    def __init__(self, src, na, nb, deg_a, rng):
        self.src = src
        self.na = na
        self.nb = nb
        self.ja = [rng.randrange(src.m) for _ in range(na)]
        self.jv = [rng.randrange(src.m) for _ in range(nb)]
        self.edges = []
        for a in range(na):
            picks = rng.sample(range(nb), deg_a)
            for v in picks:
                self.edges.append((a, v))
        self.at_a = [[] for _ in range(na)]
        self.at_v = [[] for _ in range(nb)]
        for ei, (a, v) in enumerate(self.edges):
            self.at_a[a].append(ei)
            self.at_v[v].append(ei)
        # per edge: local window T_e, offsets, selector table
        self.T = []
        self.delta_coeff = []
        self.c_coeff = []
        self.sel = []
        for (a, v) in self.edges:
            T = sorted({self.ja[a], self.jv[v]})
            self.T.append(T)
            self.delta_coeff.append([rng.randrange(2) for _ in T])
            self.c_coeff.append([rng.randrange(2) for _ in T])
            # selector: view is exactly T (parity faithful when T is cycle free)
            table = {}
            for view in range(1 << len(T)):
                table[view] = [rng.randrange(2) for _ in range(2)]  # indexed by tau
            self.sel.append(table)
        # dependency sets
        self.N_a = [sorted(set().union(*[set(self.T[e]) for e in self.at_a[a]]))
                    for a in range(na)]
        self.N_v = []
        for v in range(nb):
            e0 = self.at_v[v][0] if self.at_v[v] else None
            if e0 is None:
                self.N_v.append([])
            else:
                a0 = self.edges[e0][0]
                self.N_v.append(sorted(set(self.N_a[a0]) | set(self.T[e0])))
        self.S = []
        for ei, (a, v) in enumerate(self.edges):
            self.S.append(sorted(set(self.N_a[a]) | set(self.N_v[v]) | set(self.T[ei])))
        self.max_S = max(len(s) for s in self.S)

    # ---- local quantities -------------------------------------------------

    def _bits(self, b, idx):
        return [(b >> j) & 1 for j in idx]

    def delta(self, ei, b):
        return sum(cc * bb for cc, bb in zip(self.delta_coeff[ei], self._bits(b, self.T[ei]))) % 2

    def cshift(self, ei, b):
        return sum(cc * bb for cc, bb in zip(self.c_coeff[ei], self._bits(b, self.T[ei]))) % 2

    def view(self, ei, b):
        val = 0
        for k, j in enumerate(self.T[ei]):
            val |= ((b >> j) & 1) << k
        return val

    def branch_ok(self, ei, b, sigma0, sigma1):
        tau = (sigma0 + self.delta(ei, b)) % 2
        want = self.sel[ei][self.view(ei, b)][tau]
        return (sigma1 + self.cshift(ei, b)) % 2 == want

    # ---- witness rules ----------------------------------------------------

    def labels_zero(self, b):
        return [(0, 0) for _ in range(self.na)]

    def labels_greedy(self, b):
        out = []
        for a in range(self.na):
            best, best_s = (0, 0), -1
            for s0 in (0, 1):
                for s1 in (0, 1):
                    sc = sum(1 for e in self.at_a[a] if self.branch_ok(e, b, s0, s1))
                    if sc > best_s:
                        best_s, best = sc, (s0, s1)
            out.append(best)
        return out

    def make_random_rule(self, rng):
        tables = []
        for a in range(self.na):
            tables.append([(rng.randrange(2), rng.randrange(2))
                           for _ in range(1 << len(self.N_a[a]))])
        def rule(b, tables=tables):
            out = []
            for a in range(self.na):
                idx = 0
                for k, j in enumerate(self.N_a[a]):
                    idx |= ((b >> j) & 1) << k
                out.append(tables[a][idx])
            return out
        return rule

    def make_cycle_rule(self, word):
        """Control: a NON-local rule, it reads one parity of the cycle code."""
        def rule(b, word=word):
            bit = bin(word & b).count("1") % 2
            return [(bit, bit) for _ in range(self.na)]
        return rule

    # ---- value ------------------------------------------------------------

    def value_of_rule(self, rule, b):
        sig = rule(b)
        tau = [0] * self.nb
        for v in range(self.nb):
            if not self.at_v[v]:
                continue
            e0 = self.at_v[v][0]
            a0 = self.edges[e0][0]
            tau[v] = (sig[a0][0] + self.delta(e0, b)) % 2
        ok = 0
        for ei, (a, v) in enumerate(self.edges):
            s0, s1 = sig[a]
            if (s0 + self.delta(ei, b)) % 2 != tau[v]:
                continue
            want = self.sel[ei][self.view(ei, b)][tau[v]]
            if (s1 + self.cshift(ei, b)) % 2 == want:
                ok += 1
        return Fraction(ok, len(self.edges))

    def coset_average(self, rule, b0):
        tot = Fraction(0)
        for z in range(1 << self.src.n):
            tot += self.value_of_rule(rule, self.src.gauge(b0, z))
        return tot / (1 << self.src.n)

    # ---- exact lift value, tiny instances only ---------------------------

    def exact_value(self, b):
        best = 0
        for sig in itertools.product([(0, 0), (0, 1), (1, 0), (1, 1)], repeat=self.na):
            for tau in itertools.product([0, 1], repeat=self.nb):
                ok = 0
                for ei, (a, v) in enumerate(self.edges):
                    s0, s1 = sig[a]
                    if (s0 + self.delta(ei, b)) % 2 != tau[v]:
                        continue
                    want = self.sel[ei][self.view(ei, b)][tau[v]]
                    if (s1 + self.cshift(ei, b)) % 2 == want:
                        ok += 1
                best = max(best, ok)
        return Fraction(best, len(self.edges))

    def decoupled_bound(self, b):
        tot = 0
        for a in range(self.na):
            best = 0
            for s0 in (0, 1):
                for s1 in (0, 1):
                    sc = sum(1 for e in self.at_a[a] if self.branch_ok(e, b, s0, s1))
                    best = max(best, sc)
            tot += best
        return Fraction(tot, len(self.edges))


# --------------------------------------------------------------------------
# experiments
# --------------------------------------------------------------------------


def find_config(args):
    """Search seeds for a source and lift whose dependency sets are cycle free."""
    for seed in range(args.seed, args.seed + args.tries):
        rng = random.Random(seed)
        src = Source(args.n, args.m, rng)
        if src.d_cyc <= args.min_cycle:
            continue
        lift = Lift(src, args.na, args.nb, args.deg, rng)
        if lift.max_S >= src.d_cyc:
            continue
        if all(src.cycle_free(S) for S in lift.S):
            return seed, src, lift
    return None, None, None


def mode_main(args):
    seed, src, lift = find_config(args)
    if src is None:
        print("no configuration found; widen --tries")
        return 1
    print(f"source seed {seed}: n={src.n} m={src.m} rank(M)={src.rank_M} "
          f"cycle scale d_cyc={src.d_cyc} cycle-code dim={len(src.cycle_basis)}")
    print(f"lift: {lift.na} A-vertices, {lift.nb} B-vertices, {len(lift.edges)} edges, "
          f"max |S_e| = {lift.max_S}")

    # 1. cycle freeness
    bad = [S for S in lift.S if not src.cycle_free(S)]
    print(f"[1] edge dependency sets cycle free: {len(lift.S) - len(bad)}/{len(lift.S)}")
    assert not bad

    reps = src.coset_reps()
    vals = [src.value(r) for r in reps]
    print(f"[.] {len(reps)} cosets of Im(M); 3LIN values "
          + ", ".join(str(v) for v in vals))

    rng = random.Random(seed + 991)
    rules = {
        "zero  (folded gauge labelling F*)": lift.labels_zero,
        "greedy (per-A-vertex local max)": lift.labels_greedy,
        "random local rule": lift.make_random_rule(rng),
    }
    failures = 0
    for name, rule in rules.items():
        avgs = [lift.coset_average(rule, r) for r in reps]
        same = all(a == avgs[0] for a in avgs)
        print(f"[2] {name:36s} coset averages "
              + ", ".join(f"{float(a):.6f}" for a in avgs)
              + ("   EQUAL" if same else "   DIFFER"))
        if not same:
            failures += 1
    print(f"[3] greedy rule average = {float(lift.coset_average(rules['greedy (per-A-vertex local max)'], reps[0])):.6f}"
          f"  (beats one half: "
          f"{lift.coset_average(rules['greedy (per-A-vertex local max)'], reps[0]) > Fraction(1,2)})")

    # 4. control: a rule that reads a cycle
    word = min(src.cycle_words, key=lambda w: bin(w).count("1"))
    crule = lift.make_cycle_rule(word)
    avgs = [lift.coset_average(crule, r) for r in reps]
    same = all(a == avgs[0] for a in avgs)
    print(f"[4] control, reads one cycle of weight {bin(word).count('1')}: "
          + ", ".join(f"{float(a):.6f}" for a in avgs)
          + ("   EQUAL (control failed)" if same else "   DIFFER (expected)"))
    if same:
        failures += 1

    # 5. control: duplicate an equation, weight-2 cycle inside a 2-local view
    src2 = Source(args.n, args.m, random.Random(seed))
    src2.rows[-1] = src2.rows[0]                      # duplicate equation 0
    checks = []
    for i in range(src2.n):
        checks.append(sum(1 << j for j in range(src2.m) if (src2.rows[j] >> i) & 1))
    src2.cycle_basis = kernel_basis(checks, src2.m)
    src2.cycle_words = [w for w in span(src2.cycle_basis) if w]
    src2.d_cyc = min(bin(w).count("1") for w in src2.cycle_words)
    src2.rank_M = rank(src2.rows)
    reps2 = src2.coset_reps()
    lift2 = Lift(src2, args.na, args.nb, args.deg, random.Random(seed))
    def dup_rule(b):
        bit = (((b >> 0) & 1) + ((b >> (src2.m - 1)) & 1)) % 2
        return [(bit, bit) for _ in range(lift2.na)]
    avgs2 = [lift2.coset_average(dup_rule, r) for r in reps2]
    same2 = all(a == avgs2[0] for a in avgs2)
    print(f"[5] control, duplicated equation gives d_cyc={src2.d_cyc}; a 2-local rule "
          f"reading both copies: " + ", ".join(f"{float(a):.6f}" for a in avgs2)
          + ("   EQUAL (control failed)" if same2 else "   DIFFER (expected)"))
    if same2:
        failures += 1

    print(f"\nfailures: {failures}")
    return 0 if failures == 0 else 1


def mode_decouple(args):
    """val(U_o) <= decoupled bound, and the decoupled bound can be vacuous."""
    rng = random.Random(args.seed)
    src = Source(8, 9, rng)
    lift = Lift(src, 3, 3, 2, rng)
    viol = 0
    tight = 0
    trials = 0
    for b in range(1 << src.m):
        v = lift.exact_value(b)
        d = lift.decoupled_bound(b)
        trials += 1
        if v > d:
            viol += 1
        if v == d:
            tight += 1
    print(f"[d1] {trials} right-hand sides: val <= decoupled bound violated {viol} times, "
          f"equality {tight} times")

    # the decoupled bound is vacuous for the selector that cancels the branch offset
    for ei in range(len(lift.edges)):
        for view in lift.sel[ei]:
            # want: g_e(view)(tau) = c_e(b) for the b's with this view, so that
            # sigma_1 = 0 always satisfies the branch condition
            bits = [(view >> k) & 1 for k in range(len(lift.T[ei]))]
            cval = sum(cc * bb for cc, bb in zip(lift.c_coeff[ei], bits)) % 2
            lift.sel[ei][view] = [cval, cval]
    worst = min(lift.decoupled_bound(b) for b in range(1 << src.m))
    print(f"[d2] with the offset-cancelling selector, min over all b of the decoupled "
          f"bound = {worst}  (vacuous iff 1)")
    exact = [lift.exact_value(b) for b in range(1 << src.m)]
    print(f"[d3] the true lift value for that selector ranges over "
          f"[{float(min(exact)):.4f}, {float(max(exact)):.4f}]; B-consistency is what "
          f"the decoupling throws away")
    return 0 if viol == 0 and worst == 1 else 1


def min_cycle_upto_6(rows, m):
    """Exact minimum cycle weight when it is at most 6, else None.

    Meet in the middle: store the XOR of every pair and of every triple.
    """
    from collections import defaultdict
    single = defaultdict(list)
    for j, r in enumerate(rows):
        single[r].append(j)
        if len(single[r]) > 1:
            return 2
    pairs = defaultdict(list)
    for i in range(m):
        for j in range(i + 1, m):
            pairs[rows[i] ^ rows[j]].append((i, j))
    for r, js in single.items():
        if r in pairs:
            return 3
    triples = defaultdict(list)
    for i in range(m):
        ri = rows[i]
        for j in range(i + 1, m):
            rij = ri ^ rows[j]
            for k in range(j + 1, m):
                triples[rij ^ rows[k]].append((i, j, k))
    for s, plist in pairs.items():
        if s == 0:
            return 4
        if s in pairs:
            for (a, b_) in plist:
                for (c, d) in pairs[s]:
                    if len({a, b_, c, d}) == 4:
                        return 4
    for s, plist in pairs.items():
        if s in triples:
            for (a, b_) in plist:
                for tr in triples[s]:
                    if len({a, b_} | set(tr)) == 5:
                        return 5
    for s, tlist in triples.items():
        if s == 0:
            return 6
        if s in triples:
            for t1 in tlist:
                for t2 in triples[s]:
                    if len(set(t1) | set(t2)) == 6:
                        return 6
    return None


def mode_regime(args):
    """The cycle scale, which is the locality budget, grows with n.

    The theorem wants two things of one source at once: a density `m/n` large
    enough that a typical coset of `Im(M)` is a NO instance of gap-3LIN, and a
    cycle code with no light word.  This measures the second as `n` grows at
    fixed density, and the first by brute force at one small `n`.
    """
    print("cycle scale at density m = 2n (exact when it is at most 6):")
    for n in (12, 20, 40, 80, 160):
        m = 2 * n
        rng = random.Random(args.seed + n)
        src_rows = []
        seen = set()
        while len(src_rows) < m:
            trip = tuple(sorted(rng.sample(range(n), 3)))
            if trip in seen:
                continue
            seen.add(trip)
            src_rows.append(sum(1 << i for i in trip))
        w = min_cycle_upto_6(src_rows, m)
        print(f"  n={n:4d} m={m:4d}   d_cyc = {w if w else '> 6'}")
    print("Light cycles disappear as n grows: the first-moment bound of the route "
          "file gives d_cyc = Omega(n) at fixed density.")

    n = 12
    print("\nmean 3LIN value of a uniformly random right-hand side (brute force):")
    for ratio in (2, 4, 8):
        m = ratio * n
        rng = random.Random(args.seed + 17 * ratio)
        src = Source(n, m, rng)
        vals = [float(src.value(rng.randrange(1 << m))) for _ in range(5)]
        print(f"  m = {ratio}n   mean value {sum(vals)/len(vals):.4f}")
    print("A typical coset falls towards one half as the density grows, so NO "
          "instances of gap-3LIN sit over the same M as the satisfiable orbit.")
    return 0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--mode", choices=["main", "decouple", "regime", "all"], default="all")
    ap.add_argument("--seed", type=int, default=20260918)
    ap.add_argument("--tries", type=int, default=4000)
    ap.add_argument("--n", type=int, default=12)
    ap.add_argument("--m", type=int, default=14)
    ap.add_argument("--na", type=int, default=6)
    ap.add_argument("--nb", type=int, default=6)
    ap.add_argument("--deg", type=int, default=2)
    ap.add_argument("--min-cycle", type=int, default=7, dest="min_cycle")
    args = ap.parse_args()
    rc = 0
    if args.mode in ("main", "all"):
        rc |= mode_main(args)
    if args.mode in ("decouple", "all"):
        print()
        rc |= mode_decouple(args)
    if args.mode in ("regime", "all"):
        print()
        rc |= mode_regime(args)
    print("\nOK" if rc == 0 else "\nFAILED")
    return rc


if __name__ == "__main__":
    raise SystemExit(main())
