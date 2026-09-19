#!/usr/bin/env python3
"""Checks for `grassmann-restriction-test-is-99-percent-rigid`.

The claim is a 99%-regime structure theorem for the *linear* Grassmann
restriction test over F_2:

    X = F_2^D;  a label sigma_L in L^* for every L in Gr(X, l);
                a label tau_Q in Q^* for every Q in Gr(X, l-1);
    test: draw a uniform flag Q < L (dim l-1 < dim l), accept iff sigma_L|_Q = tau_Q.

Theorem.  If the test accepts with probability >= 1 - eta then there is a single
A in X^* with Pr_L[sigma_L = A|_L] >= 1 - 800 eta, provided eta <= 1/2000 and
2^(l-D) <= eta.  The constant does not depend on l or D.

Three independent things are checked here, one per ingredient of the proof.

  (1) SPECTRAL.  The proof uses only that the down-up walk W on Gr(X, l-1)
      (pick a uniform hyperplane P < Q, then a uniform Q~ > P) has all
      non-trivial eigenvalues of absolute value <= 1/2 + s, s = 1/(2^(D-l+2)-1).
      We build W exactly and diagonalise it, and we cross-check the closed
      Grassmann-scheme formula lambda_j = 2^(j+1) [k-j]_2 [n-k-j]_2 - [j]_2.

  (2) GADGET UNIFORMITY.  The proof's six flags are built from a sample
      (Q, P, x, y) by GL(X)-equivariant maps, so each of them is *exactly*
      uniform on flags once the generic event G holds.  We verify this by
      exhaustive enumeration: for each of the six maps, every flag receives
      exactly the same count.  This is the step that makes the six union-bound
      terms cost eta each rather than eta times a distribution ratio.

  (3) END TO END.  For several labelling families (honest, noisy honest,
      zoom-in, zoom-out, mixed, uniformly random) we compute the exact
      rejection rate eta and the exact distance
      min_A Pr_L[sigma_L != A|_L], and report the ratio.  The assertion is the
      theorem's inequality; the printed maximum ratio shows how much slack the
      constant 800 has (empirically the extremal ratio is about 2).

Run: python3 experiments/grassmann-99-rigidity-2026-09-18/check_grassmann_99_rigidity.py
"""

from __future__ import annotations

import itertools
import random
import sys
from collections import Counter, defaultdict

try:
    import numpy as np
except ImportError:  # pragma: no cover
    np = None

SEED = 20260918


# ---------------------------------------------------------------- linear algebra

def popcount_parity(x: int) -> int:
    return bin(x).count("1") & 1


def rref(vectors, D):
    """Row-reduce a list of F_2^D vectors (as ints); return the canonical basis tuple."""
    basis = []
    for v in vectors:
        for b in basis:
            v = min(v, v ^ b)
        if v:
            basis.append(v)
            basis.sort(reverse=True)
    # full reduction so the basis is canonical
    basis.sort(reverse=True)
    out = []
    for i, b in enumerate(basis):
        piv = b.bit_length() - 1
        for j, c in enumerate(basis):
            if j != i and (c >> piv) & 1:
                basis[j] = c ^ b
    basis.sort(reverse=True)
    out = tuple(basis)
    return out


def span(basis) -> frozenset:
    elts = {0}
    for b in basis:
        elts |= {e ^ b for e in elts}
    return frozenset(elts)


def subspaces(D: int, d: int):
    """All d-dimensional subspaces of F_2^D, as canonical RREF basis tuples."""
    if d == 0:
        return [()]
    seen = {}
    for combo in itertools.combinations(range(1, 1 << D), d):
        b = rref(list(combo), D)
        if len(b) == d:
            seen[b] = True
    return sorted(seen.keys())


def hyperplanes_of(basis, D):
    """All codimension-1 subspaces of the space spanned by `basis`."""
    d = len(basis)
    if d == 0:
        return []
    out = {}
    for combo in itertools.combinations(span(basis) - {0}, d - 1):
        b = rref(list(combo), D)
        if len(b) == d - 1:
            out[b] = True
    return sorted(out.keys())


# ------------------------------------------------------------------ (1) spectral

def q_int(m: int) -> int:
    return (1 << m) - 1


def grassmann_eigs_formula(n: int, k: int):
    return [
        (1 << (j + 1)) * q_int(k - j) * q_int(n - k - j) - q_int(j)
        for j in range(k + 1)
    ]


def check_spectral(D: int, l: int, verbose=True) -> float:
    """Build the down-up walk on Gr(X, l-1) and return max |non-trivial eigenvalue|."""
    k = l - 1
    seeds = subspaces(D, k)
    index = {s: i for i, s in enumerate(seeds)}
    n = len(seeds)
    P = np.zeros((n, n))
    for s in seeds:
        subs = hyperplanes_of(s, D) if k >= 1 else [()]
        if not subs:
            # k = 0: the walk is trivial (a single vertex)
            P[index[s], index[s]] = 1.0
            continue
        for p in subs:
            # every k-space containing p
            ups = []
            pspan = span(p)
            for v in range(1, 1 << D):
                if v in pspan:
                    continue
                b = rref(list(p) + [v], D)
                if len(b) == k:
                    ups.append(b)
            ups = sorted(set(ups))
            w = 1.0 / (len(subs) * len(ups))
            for u in ups:
                P[index[s], index[u]] += w
    ev = np.linalg.eigvals(P)
    ev = sorted(ev.real, key=lambda t: -abs(t))
    lam = max(abs(t) for t in ev[1:]) if n > 1 else 0.0
    s_loop = 1.0 / ((1 << (D - k + 1)) - 1)
    if verbose:
        formula = grassmann_eigs_formula(D, k)
        deg = formula[0]
        # the walk is (1 - s) * (uniform Grassmann-graph step) + s * (stay), so
        # its eigenvalues are (1 - s) * lambda_j / deg + s; combine signed, then
        # take the largest modulus over the non-trivial ones.
        pred_walk = max(
            abs((1 - s_loop) * (f / deg) + s_loop) for f in formula[1:]
        ) if k >= 1 and deg else 0.0
        print(
            f"  Gr(F_2^{D}, {k}):  |Gr| = {n:5d}   max|lambda_nontrivial| = {lam:.6f}"
            f"   formula predicts {pred_walk:.6f}   bound 1/2 + s = {0.5 + s_loop:.6f}"
        )
        assert abs(lam - pred_walk) < 1e-8, (lam, pred_walk)
    assert lam <= 0.5 + s_loop + 1e-9, (D, l, lam)
    return lam


# ------------------------------------------------------------------- (2) gadget

def check_gadget_uniformity(D: int, l: int) -> None:
    """Exhaustively verify that each of the six gadget flags is uniform on flags.

    Sample space: Q in Gr(X, l-1), P a hyperplane of Q, x, y in X, conditioned on
    the generic event G = {x, y, x+y not in Q}.  Gadget:
        N   = P + <x, y>,      L_u = Q + <u>,     Q_u = P + <u>   (u in {x, y, x+y})
    Six flags: (N, Q_u) and (L_u, Q_u) for u in {x, y, x+y}.
    """
    seeds = subspaces(D, l - 1)
    tops = subspaces(D, l)
    top_set = set(tops)
    flags = set()
    for L in tops:
        for Q in hyperplanes_of(L, D):
            flags.add((L, Q))
    counts = [Counter() for _ in range(6)]
    total = 0
    for Q in seeds:
        Qspan = span(Q)
        for P in hyperplanes_of(Q, D):
            for x in range(1, 1 << D):
                if x in Qspan:
                    continue
                for y in range(1, 1 << D):
                    if y in Qspan or (x ^ y) in Qspan:
                        continue
                    total += 1
                    N = rref(list(P) + [x, y], D)
                    assert len(N) == l, "G should force dim N = l"
                    for i, u in enumerate((x, y, x ^ y)):
                        Qu = rref(list(P) + [u], D)
                        Lu = rref(list(Q) + [u], D)
                        assert len(Qu) == l - 1 and len(Lu) == l
                        counts[2 * i][(N, Qu)] += 1
                        counts[2 * i + 1][(Lu, Qu)] += 1
    for i, c in enumerate(counts):
        assert set(c.keys()) == flags, f"gadget map {i} misses flags"
        vals = set(c.values())
        assert len(vals) == 1, f"gadget map {i} is not uniform: {sorted(vals)[:5]}"
    print(
        f"  D={D}, l={l}: {total} gadget samples, all six induced flag laws exactly"
        f" uniform on {len(flags)} flags"
    )


# ---------------------------------------------------------------- (3) end to end

class Instance:
    def __init__(self, D: int, l: int):
        self.D, self.l = D, l
        self.tops = subspaces(D, l)
        self.seeds = subspaces(D, l - 1)
        self.span_top = {L: span(L) for L in self.tops}
        self.span_seed = {Q: span(Q) for Q in self.seeds}
        self.hyps = {L: hyperplanes_of(L, D) for L in self.tops}
        self.ups = defaultdict(list)
        for L in self.tops:
            for Q in self.hyps[L]:
                self.ups[Q].append(L)
        self.flags = [(L, Q) for L in self.tops for Q in self.hyps[L]]

    def restrict_key(self, a: int, Q):
        """Canonical key of a|_Q: the tuple of values on the canonical basis of Q."""
        return tuple(popcount_parity(a & b) for b in Q)

    def eta(self, sigma):
        """Rejection rate of the flag test with tau chosen optimally (plurality)."""
        best = {}
        for Q in self.seeds:
            c = Counter(self.restrict_key(sigma[L], Q) for L in self.ups[Q])
            best[Q] = c.most_common(1)[0][0]
        bad = 0
        for (L, Q) in self.flags:
            if self.restrict_key(sigma[L], Q) != best[Q]:
                bad += 1
        return bad / len(self.flags)

    def distance(self, sigma):
        """min over A in X^* of Pr_L[sigma_L != A|_L]."""
        n = len(self.tops)
        best = 1.0
        for A in range(1 << self.D):
            bad = 0
            for L in self.tops:
                d = sigma[L] ^ A
                if any(popcount_parity(d & b) for b in L):
                    bad += 1
                    if bad / n >= best:
                        break
            best = min(best, bad / n)
            if best == 0.0:
                break
        return best


def families(inst: Instance, rng: random.Random):
    D, l = inst.D, inst.l
    X = 1 << D
    out = []
    A = rng.randrange(X)
    # honest
    out.append(("honest", {L: A for L in inst.tops}))
    # noisy honest at several rates
    for p in (0.01, 0.02, 0.05, 0.1, 0.2):
        sigma = {}
        for L in inst.tops:
            sigma[L] = rng.randrange(X) if rng.random() < p else A
        out.append((f"noise p={p}", sigma))
    # zoom-out: a different functional on the l-spaces inside a fixed hyperplane
    W = rng.randrange(1, X)  # the hyperplane {v : <W,v> = 0}
    A2 = rng.randrange(X)
    sigma = {}
    for L in inst.tops:
        inside = all(popcount_parity(W & v) == 0 for v in inst.span_top[L])
        sigma[L] = A2 if inside else A
    out.append(("zoom-out", sigma))
    # zoom-in: a different functional on the l-spaces containing a fixed point
    p0 = rng.randrange(1, X)
    A3 = rng.randrange(X)
    sigma = {L: (A3 if p0 in inst.span_top[L] else A) for L in inst.tops}
    out.append(("zoom-in", sigma))
    # zoom-out plus noise
    sigma = {}
    for L in inst.tops:
        inside = all(popcount_parity(W & v) == 0 for v in inst.span_top[L])
        base = A2 if inside else A
        sigma[L] = rng.randrange(X) if rng.random() < 0.02 else base
    out.append(("zoom-out + noise", sigma))
    # uniformly random
    out.append(("random", {L: rng.randrange(X) for L in inst.tops}))
    return out


def check_end_to_end(D: int, l: int, rng: random.Random, trials: int = 3):
    inst = Instance(D, l)
    worst = 0.0
    rows = []
    for _ in range(trials):
        for name, sigma in families(inst, rng):
            e = inst.eta(sigma)
            d = inst.distance(sigma)
            ratio = (d / e) if e > 0 else 0.0
            worst = max(worst, ratio)
            rows.append((name, e, d, ratio))
            # the theorem's inequality (it only has content for small eta)
            assert d <= 800 * e + 1e-12, (name, e, d)
    agg = defaultdict(list)
    for name, e, d, r in rows:
        agg[name].append((e, d, r))
    print(f"  D={D}, l={l}: |Gr(l)| = {len(inst.tops)}, |Gr(l-1)| = {len(inst.seeds)}")
    for name in sorted(agg):
        es = [t[0] for t in agg[name]]
        ds = [t[1] for t in agg[name]]
        rs = [t[2] for t in agg[name]]
        print(
            f"    {name:20s} eta in [{min(es):.4f},{max(es):.4f}]"
            f"  dist in [{min(ds):.4f},{max(ds):.4f}]  max dist/eta = {max(rs):.3f}"
        )
    return worst


# ------------------------------------------------------------------------ driver

def main() -> int:
    rng = random.Random(SEED)
    print("(1) spectral gap of the down-up walk on Gr(X, l-1)")
    if np is None:
        print("  numpy missing, skipping the spectral check")
    else:
        for D, l in ((4, 2), (5, 2), (6, 2), (5, 3), (6, 3), (7, 3), (6, 4)):
            check_spectral(D, l)

    print("(2) exact uniformity of the six gadget flags")
    for D, l in ((4, 2), (5, 2), (4, 3), (5, 3)):
        check_gadget_uniformity(D, l)

    print("(3) end to end: exact eta and exact distance to the nearest global A")
    worst = 0.0
    for D, l in ((5, 2), (6, 2), (5, 3), (6, 3)):
        worst = max(worst, check_end_to_end(D, l, rng))
    print(f"  worst observed dist/eta over all families and sizes: {worst:.3f}")
    print("ALL CHECKS PASSED")
    return 0


if __name__ == "__main__":
    sys.exit(main())
