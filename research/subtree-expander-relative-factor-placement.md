---
rg: 2
id: subtree-expander-relative-factor-placement
kind: claim
title: Sibling signs occupy an expander spin factor and its relative commutant
distinct_from:
  nekrashevych-clifford-sign-tape: that asks for the complete finite self-similar group and exact marked model; this isolates the one algebraic placement property needed for trace independence after local rounding.
  uniform-relative-clifford-tape-cell: that proves rank-independent relative exactification for sequential Toeplitz cells; this asks the self-similar sibling recursion to expose the same tensor-factor placement.
---

In the self-similar sign tape, choose fixed Jacobi/expander word templates so
that, on every level and every sufficiently accurate finite-dimensional
tuple, uniform relative exactification identifies a large carrier with

```text
M_N tensor M_r
```

where the first sibling sign is `O(sqrt(E))`-close to `M_N tensor I_r`, the
second sibling sign has average squared commutator at most `C E` with the
fixed expander unitaries on `M_N`, and discarded trace is at most `C E`.
All constants must be independent of the level, `N`, and `r`.

This is an algebraic word-placement claim, not an additional mixing estimate:
`expander-separated-factors-have-independent-traces` supplies the latter.

## Attempts

- Reuse the sequential placement already proved by
  `uniform-relative-clifford-tape-cell`: the old Clifford prefix is the spin
  factor and the newly exactified Pauli cell acts on its residual
  multiplicity.  What is not yet verified is that the two *sibling* section
  words of one self-similar cocycle coincide with those sequential factors.
- Disjoint cylinder support is insufficient.  It gives commutation but permits
  perfectly correlated central summands, so the placement must name the
  Jacobi expander on one sibling and put the other in its certified relative
  commutant by actual relators.
