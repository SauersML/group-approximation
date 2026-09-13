---
rg: 2
id: sl4z-reduced-cstar-is-not-mf
kind: claim
title: The reduced C-star algebra of SL_4(Z) is not MF
distinct_from:
  sl4z-representations-have-sl2-invariant-vectors: that excludes strongly convergent genuine finite-dimensional representations; this excludes every MF embedding, including asymptotic homomorphisms that are not near representations.
root: true
---

**Root (2026-09-13, ex-steward).** Magee--de la Salle, arXiv:2312.03220v2, p. 2, quoted below: MF-ness of `C*_r(SL_4(Z))` is not known. This claim is its negative side.

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
* **Corona norm four (ex3-sl4z-mf, 2026-09-13, unreviewed).**  Live.
  - `sl4z-reduced-not-mf-from-corona-block-sl2-norm-four` needs only
    `sl4z-corona-representations-have-block-sl2-norm-four`: norm four for the block
    `SL_2(Z)` Laplacian in every corona representation.  Matricial stability implies it.
  - It holds whenever the column unipotent spectrum is not all of `T^3`
    (`sl4z-block-sl2-norm-four-unless-unipotent-spectrum-is-full`).
  - MF embeddings have full spectrum.  There, Magee--de la Salle's averaging at
    non-torsion characters gives only spectral gap
    (`mdls-averaging-at-non-torsion-character-gives-spectral-gap`).
