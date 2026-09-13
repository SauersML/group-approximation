---
rg: 2
id: pure-braid-middle-bnsr-invariants-computed
kind: claim
title: "The intermediate BNSR invariants Sigma^m(P_n), 2 <= m <= n-3, have an explicit description"
distinct_from:
  zaremsky-1-09-bnsr-invariants-of-pure-braid-groups: that claim is the full question; this is only the intermediate range, the one part still open.
  pure-braid-top-bnsr-invariants-are-center-nonvanishing: that claim settles m >= n-2; this is the range 2 <= m <= n-3 below it.
artifacts:
  - research/artifacts/zp-pure-braid-bnsr-middle-range-2026-09-13.md
---

For every `n >= 5` and `2 <= m <= n - 3`, the complement of `Sigma^m(P_n)` in
`S(P_n)` is the unit sphere of an explicitly given finite union of rational
linear subspaces of `Hom(P_n, R)`, described by equations in the coefficients
`a_{ij}` of `chi = sum a_{ij} omega_{ij}`.

This is the part of Zaremsky Problem 1.9 that is still open: `m = 1` is
Koban–McCammond–Meier, and `m >= n - 2` is
`pure-braid-top-bnsr-invariants-are-center-nonvanishing`.

## Attempts

- Outside the invariants: `pure-braid-product-projections-obstruct-bnsr-invariants`
  (block-supported zero-sum characters), Zaremsky's `chi_n^m`, and the
  resonance upper bound `arrangement-bnsr-invariants-avoid-real-resonance`.
- Inside the invariants: Zaremsky Proposition 5.6 (exactly one coefficient of
  one sign, none zero, zero sum: in `Sigma^{n-3}`); Kohno–Pajitnov Theorem 2.4
  (positive classes in affine charts of `M_{0,n+1}`, homologically); induction
  along natural projections for discrete characters (Zaremsky, proof of
  Theorem 5.7).
- Route in progress: resonance sharpness plus an explicit computation of the
  higher resonance varieties (`pure-braid-middle-bnsr-from-resonance-sharpness`).
- Smallest open case: `Sigma^2(P_5)`.
