---
rg: 2
id: atlas-block-circulant-mode-promotion-proof
kind: route
title: Pass cyclic residuals to primary Fourier quotients
target: atlas-block-circulant-joint-escape-promotes-to-exact-mode
requires:
  - atlas-repeated-h6-gauge-is-one-gl2m-coordinate
  - atlas-exact-matrix-zero-set-is-a-finite-quotient-test
  - atlas-q14-adds-stratified-thirteenth-double-coset
---

Write `N=eM`, where `e` is the largest power of two dividing `N`, and extend
scalars to an algebraic closure `K` of `F2`.  Then

```text
K[C_N]=K[z]/(z^N-1)
      =product_(zeta^M=1) K[epsilon]/(epsilon^e),       (BCP1)
```

with `z=zeta+epsilon` in the `zeta` factor.  A unit block-circulant gauge
reduces to an invertible matrix `T(zeta)` in every residue field.  Inversion,
packet evaluation, and both kernel-word evaluations commute with this
reduction because they are matrix-valued Laurent expressions in the gauge.

Let `R` be any one of the finitely many residual matrices.  The epsilon-adic
filtration of the `zeta` primary block is preserved by `R`, and every one of
its `e` associated-graded maps is `R(T(zeta))`.  The flag kernel inequality
therefore gives

```text
rank_K R(T_N) >= e sum_(zeta^M=1) rank_K R(T(zeta)).   (BCP2)
```

Rank is unchanged by scalar extension.  If the left side is `o(N)=o(eM)`,
only `o(M)` modes can have nonzero residue.  Taking the union of the bad-mode
sets for the fixed finite packet menu and the two kernel words still leaves a
common good mode when `M` tends to infinity.  If `M` stays bounded, `(BCP2)`
and integrality force every mode residual to vanish for all sufficiently large
indices.  Thus in either case a common exact invertible mode exists.

Its entries are algebraic over a finite field, hence belong to some finite
extension `F_(2^f)`.  Restrict scalars to `F2` and apply the exact-matrix
zero-set/finite-quotient theorem.  This proves `(BCJ1)`.

