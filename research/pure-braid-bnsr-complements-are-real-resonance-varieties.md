---
rg: 2
id: pure-braid-bnsr-complements-are-real-resonance-varieties
kind: claim
title: "Conjecture: every BNSR invariant Sigma^m(P_n) is the complement of the real resonance variety R^{<=m}(P_n)"
distinct_from:
  arrangement-bnsr-invariants-avoid-real-resonance: that claim is the upper bound (the invariant avoids resonance) for all arrangements; this asserts equality for the braid arrangement in every degree.
artifacts:
  - research/artifacts/zp-pure-braid-bnsr-middle-range-2026-09-13.md
---

For all `n >= 1` and `m >= 1`,

    Sigma^m(P_n) = S(P_n) \ S(R^{<=m}(P_n; R)),

where `R^{<=m}` is the union of the resonance varieties `R^i` (`i <= m`) of the
Orlik–Solomon algebra of the braid arrangement and `R(...; R)` denotes real
points. One inclusion is `arrangement-bnsr-invariants-avoid-real-resonance`;
the content is the other one (every non-resonant character lies in
`Sigma^m`).

## Attempts

- Holds for `m = 1`: Koban–McCammond–Meier Theorem A, with Cohen–Suciu 1999
  Proposition 6.9 identifying the circles with `R^1` (Suciu arXiv:2010.07499,
  Example 13.2).
- Holds for `m >= n - 2`: `pure-braid-top-bnsr-invariants-are-center-nonvanishing`.
  `R^{<=m}(P_n)` is the zero-sum hyperplane there: the Aomoto complex of
  `M_{0,n+1}` has Euler characteristic `(-1)^n (n-2)!`, and for nonzero sum the
  complex of `P_n` is exact.
- Compatible with `pure-braid-product-projections-obstruct-bnsr-invariants`:
  those characters are resonant in degrees `<= D` (retract of the Aomoto
  complex of the quotient).
- Caveat: for the deleted `B_3` arrangement, `Sigma^1 != S(R^1)^c` because of
  translated tori (Suciu Proposition 13.6). So the conjecture includes the
  assertion that translated components of `V^m` for the braid arrangement do
  not tropicalize outside `R^m`.
- First open test: `n = 5`, `m = 2`. Predicted complement: six 4-spheres (five
  zero-sum 4-strand subspaces plus the `S_6`-symmetric "row sums zero"
  subspace). Membership for characters off these spheres is unproved.
