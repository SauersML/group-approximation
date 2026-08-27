---
rg: 2
id: thin-quasiregular-profile-promotes-to-liftable-charts
kind: claim
title: A matrix-origin co-dense quasiregular profile promotes to positive-density liftable permutation charts
root: true
distinct_from:
  thin-selected-leak-amplifies-to-codense-quasiregular-profile: that produces one HS-approximable coefficient 1_H from a selected leak; this asks for the additional common-carrier chart family required for a sofic action.
  stable-finite-actions-blocks-codense-kazhdan-coset-soficity: that rules out a sofic atlas after assuming stability in finite actions; this is the opposite promotion step from unitary coefficient microstates to such an atlas.
---

Let `A=SL_3(Z)` and let `C=<a,b>` be the explicit thin profinitely dense
subgroup.  Suppose `C<=H<A` and there are normalized-HS asymptotic unitary
representations `beta_n` with unit vectors `xi_n` satisfying

```text
<beta_n(g)xi_n,xi_n> -> 1_H(g).                        (QPC1)
```

Assert that `(QPC1)` can be promoted to a permutation-ultraproduct
homomorphism and liftable label maps `(LHC1)`--`(LHC2)` for

```text
A curvearrowright A/H.                                 (QPC2)
```

By `gkp-sofic-action-is-liftable-hamming-chart-family`, this is exactly the
assertion that the coset action is sofic.

## Attempts

- The orbit vectors `beta_n(x)xi_n` have asymptotically the correct Gram
  matrix on every fixed finite subset of `A/H`.  This gives one Hilbert chart
  at one root, not charts on density `1-o(1)` of a common permutation
  carrier.
- Tensor powers do not add the missing data:
  `tensor-root-profile-adds-no-chart-coherence` shows
  that `1_H` is idempotent under every scalar tensor amplification.
- A covariant measurement of finitely many almost-orthogonal orbit states
  can label one finite window, but no known argument makes the measurement
  monomial for the actor or supplies the positive-density covariance in
  `(LHC2)`.  Doing so is a permutation-stability/rounding theorem, not a
  state-discrimination estimate.
- Property `(T)` controls almost invariant vectors after one already has a
  representation.  It does not turn arbitrary unitary matrices into
  permutations or manufacture a commutative carrier algebra.  Existing
  stability-in-finite-actions results do not cover the nonnormal inclusion
  `H<A`.
- Even global normalized-HS exactification is insufficient at this reduced
  coefficient level: `spectator-dilution-hides-root-profile-from-hs-correction`
  makes the selected root live on a vanishing-dimensional summand while the
  whole model becomes HS-close to the exact trivial representation.  A
  successful correction must control the selected vector or a
  positive-density chart sector.
- Gao--Kunnawalkam Elayavalli--Patchell explicitly leave open whether all
  actions of sofic groups are sofic and whether soficity of generalized
  wreath products forces soficity of the underlying action.  The present
  promotion would cross that same unitary-to-permutation boundary in a
  property-`(T)`, co-dense special case.

**Status: OPEN.**
