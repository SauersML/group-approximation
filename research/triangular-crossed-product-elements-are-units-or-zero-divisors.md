---
rg: 2
id: triangular-crossed-product-elements-are-units-or-zero-divisors
kind: claim
title: An odd-measure crossed-product element whose column peeling stops is a left zero divisor, and one whose peeling terminates is a unit
distinct_from:
  monomial-crossed-product-elements-are-units-or-zero-divisors: that is the one-round case, under column weight or image multiplicity at most one; this runs the peeling for finitely many rounds and reaches honest lifts with column weight three.
artifacts:
  - research/artifacts/crossed-product-zero-divisor-filters-2026-09-12.md
---

Let `B = C(M_-, F_3) x| V` and `x = sum_g [g] b_g in B`. In the fibre at `mu`, the column `k` has points
`gk` with `b_g(k mu) != 0`.

**Peeling.** Start with every column and point live. In each round:
- if some live column has no live point, or two live columns with exactly one live point share it,
  the peeling *stops*;
- otherwise every live column with exactly one live point is removed together with that point.

Each round is decided by `k mu` through finitely many locally constant functions, so it is uniform in
`mu`. The peeling *terminates* if every column is removed by some round `r_0` and no fibre ever stops.

**Theorem.**
1. If the peeling stops in some fibre, `x` is a left zero divisor, by back-substitution and
   `crossed-product-zero-divisors-are-detected-on-fibres`.
2. If it terminates, `x` is a unit. `x = D(1 + D^-1 N)`, with `D` the signed permutation of diagonal
   entries and `D^-1 N` nilpotent of order at most `r_0`.
3. Otherwise, after every round the live columns form a nonempty clopen set of the same Haar measure as
   the live points. A round that removes nothing leaves every live column with at least two live points.

**Consequences.**
- *Witness entries.* A Cohn isometry `sigma_j`, or a corner witness `q_[0] b'`, that lies in `B` has a
  peeling that neither stops nor terminates. So does `tau*` for a co-isometry `tau` lying in `B`.
- *Beyond Theorem 3.1.* The three-piece honest lift of `s_0`,
  `[g_1]P_00 + [g_2]P_01 + [g_3]P_1` (Example 4.3 of the artifact), has column weight `3` on
  `U_00 ∩ U_01 ∩ U_1`, so the monomial dichotomy does not apply. Its peeling stops in round two, so it is
  a left zero divisor.

Theorem 4.1, Corollary 4.2 and Example 4.3 of the artifact.

**ESTABLISHED 2026-09-12** by `triangular-crossed-product-peeling-proof`.
