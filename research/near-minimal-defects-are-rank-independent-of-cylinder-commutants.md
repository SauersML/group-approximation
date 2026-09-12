---
rg: 2
id: near-minimal-defects-are-rank-independent-of-cylinder-commutants
kind: claim
title: At near-minimal defect a two-root cylinder defect is rank-independent of every element commuting with its cylinder group
distinct_from:
  near-minimal-defect-models-have-multiplicative-cylinder-defects: that shows products of disjoint cylinder defects have independent-tensor ranks at near-minimal defect; this extends the same conclusion to products with an arbitrary element of the commutant of the cylinder group, including the group algebra of the complementary model.
  leavitt-disjoint-cylinder-defects-strictly-submultiplicative: that is the open strict deficit; this is an established two-sided bound that pins such products to independence at the infimum, so any deficit must come from ranks the theorem does not fix.
artifacts:
  - research/artifacts/cylinder-commutant-independence-and-weyl-firewall-2026-09-12.md
---

**ESTABLISHED** (route `near-minimal-commutant-independence-proof`; artifact Section 2; independent
re-derivation requested from `w4-vf-gate`).

**Statement.**
* **Setting.** `sigma` is a nontrivial fixed-point-free characteristic-two rank model of
  `R^x = L_(F_2)(1,2)^x`, `delta = rk(D_1000)`, and `c_*` is the infimum of the normalized defect over
  such models. `A` is a proper cylinder and `X` is any element of the rank ultraproduct commuting with
  `sigma(iota_A(R^x))`.
* **Conclusion.** For every proper prefix `P`,

  ```text
  c_* rk(X)  <=  rk(D_(AP) X)  <=  delta - c_* (1 - rk(X)) .
  ```

  So `|rk(D_(AP) X) - delta rk(X)| <= eps delta` when `delta <= (1+eps) c_*`, with equality
  `rk(D_(AP) X) = delta rk(X)` at `delta = c_*`.

**Special cases.**
* `X` a product of disjoint defects: `near-minimal-defect-models-have-multiplicative-cylinder-defects`.
* `X` an idempotent of an invariant decomposition: at the infimum both summands carry normalized defect
  exactly `c_*`.
* `X` in the image of `F_2[iota_E(R^x)]` for the complement `E` of `A`: independence from a whole
  fixed-point-free model of `R^x`.

**Where it stops.** Products only. Ranks of sums across `iota_A` and its commutant, such as the doubled
defect that the halving relation makes conjugate to a single defect, are not fixed by this theorem.

## Attempts

- Established, not open. Proof: range corner and kernel corner of `X` are fixed-point-free models by
  globality on cylinders, plus the triangular rank count through `rk(XJ) = rk(J) - rk(K)`.
