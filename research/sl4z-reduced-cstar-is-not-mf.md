---
rg: 2
id: sl4z-reduced-cstar-is-not-mf
kind: claim
title: The reduced C-star algebra of SL_4(Z) is not MF
distinct_from:
  sl4z-representations-have-sl2-invariant-vectors: that excludes strongly convergent genuine finite-dimensional representations; this excludes every MF embedding, including asymptotic homomorphisms that are not near representations.
---

OPEN.  `C*_r(SL_4(Z))` admits no injective *-homomorphism into a norm matrix
corona `prod_n M_(k_n) / sum_n M_(k_n)`.

Magee--de la Salle write that it "does not seem to be known whether
C*_r(SL3(Z)) or C*_r(SL4(Z)) is MF" (arXiv:2312.03220v2, p. 2).  A proof
would show that no group containing `SL_4(Z)` has MF reduced algebra, which
bears on `kt-double-reduced-cstar-is-mf` when its vertex contains `SL_d(Z)`
with `d >= 4`.

## Attempts

* **From genuine representations.**  Only half the claim:
  `sl4z-representations-have-sl2-invariant-vectors` excludes strongly
  convergent genuine representations, not asymptotic homomorphisms.
* **Through matricial stability.**  Live and conditional:
  `sl4z-reduced-not-mf-from-matricial-stability`.
* **Approximate fixed vectors.**  Not worked.  The Magee--de la Salle proof
  runs through torsion characters of the unipotent subgroup `Z^3` of
  `SL_4(Z/NZ)` and their large stabilizers; an asymptotic homomorphism need not
  have a torsion joint spectrum on `Z^3`, so the argument does not transfer
  directly.
