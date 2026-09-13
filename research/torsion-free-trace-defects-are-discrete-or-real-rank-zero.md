---
rg: 2
id: torsion-free-trace-defects-are-discrete-or-real-rank-zero
kind: claim
title: A torsion-free trace defect is either rational with bounded denominator or produces a torsion-free group whose reduced C*-algebra has real rank zero
distinct_from:
  free-product-kk-iff-trace-conjecture-for-factors: that computes the projection traces of C*_r(G * Z); this sorts the possible trace images into three cases and identifies the dense case with real rank zero.
  selfless-real-rank-zero-iff-dense-k0-traces: that is the operator-algebra criterion; this is its consequence for torsion-free groups and the Kadison--Kaplansky root.
---

**ESTABLISHED** by `torsion-free-trace-defects-are-discrete-or-real-rank-zero-proof`.

**Theorem (trichotomy).** Let `G` be a nontrivial countable torsion-free group and `S = τ_*(K_0(C*_r G))`.
Exactly one of the following holds.
1. `S = Z`. The trace conjecture holds for `G`, and `C*_r(G * Z)` has no projection other than `0, 1`.
2. `S = (1/m)Z` for some `m >= 2`. The projections of `C*_r(G * Z)` have traces exactly `k/m`,
   `0 <= k <= m`, so Kadison--Kaplansky fails on `G * Z`, and `C*_r(G * Z)` does not have real rank zero.
3. `S` is dense in `R`. Then `C*_r(G * Z)` has real rank zero.

**Corollary (real rank zero form of the root).** The following are equivalent.
- (a) Some countable torsion-free group has a `K_0` trace image that is not discrete, for example one
  containing an irrational number.
- (b) Some countable torsion-free group has a reduced C\*-algebra of real rank zero.

Both refute `kadison-kaplansky-torsion-free`. So a counterexample to the root is either **arithmetic**
(bounded denominators) or **real rank zero**.

**Model tests with torsion,** where the same computation runs.
- `G = C_2`: `S = (1/2)Z`, and `C*_r(C_2 * Z)` has projections of traces `0, 1/2, 1` only.
- `G = *_(n>=2) C_n`: `S ⊇ sum_n (1/n)Z = Q`, which is dense, so `C*_r(G * Z)` has real rank zero. This
  agrees with Dykema--Rørdam II for infinite free products.
- `G = Z`: `S = Z`, giving `C*_r(F_2)` with no nontrivial projection (Pimsner--Voiculescu).
