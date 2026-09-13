---
rg: 2
id: free-group-crossed-product-matricial-iff-invariant-measure-proof
kind: route
title: Measure to residual finiteness (Kerr–Nowak), to matricial (towers), to rank function, back to measure
target: free-group-crossed-product-matricial-iff-invariant-measure
requires: [kerr-nowak-measure-free-group-actions-are-rf, residually-finite-actions-give-matricial-crossed-products, matricial-steinberg-algebras-have-invariant-measures]
artifacts:
  - research/artifacts/un-measure-residually-finite-lef-rings-2026-09-13-part2.md
---

Artifact part 2, §4.
- (i) ⇒ (ii): `kerr-nowak-measure-free-group-actions-are-rf`.
- (ii) ⇒ (iii): `residually-finite-actions-give-matricial-crossed-products`.
- (iii) ⇒ (iv): trivial.
- (iv) ⇒ (v): pull back the normalized ultraproduct rank
  (`matricial-steinberg-algebras-have-invariant-measures`, item 1).
- (v) ⇒ (i): `μ(U) = rk(1_U)` is finitely additive and invariant under the bisections `u_g 1_U`, and
  extends to a Borel probability measure. This is the argument of item 2 of the same claim, which
  uses only a unital Sylvester rank function.
