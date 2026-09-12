---
rg: 2
id: hilbert-hotel-prescribed-mf-reflection-proof
kind: route
title: Take a direct product with the desired visible group
target: hilbert-hotel-prescribed-mf-reflection
requires:
  - hilbert-hotel-model-full-mf-radical
  - hilbert-hotel-block-cover-is-unconditional
  - full-mf-radical-absorber
  - reduced-cstar-mf-black-hole-absorption
artifacts:
  - research/hilbert-hotel-prescribed-mf-reflection.md
---

Apply the absorber formula to the inclusion of `H` as the first direct
factor.  The quotient is `B`, and `Rad_MF(B)=1` because `B` is MF.  The
preimage formula gives `(P1)`.

Direct products preserve finite generation and finite presentation.  The
rank-sixteen model supplies the finitely generated statement; the
finitely-presented full-radical Hilbert-hotel cover supplies the finitely
presented statement.

Finally `H` embeds as a subgroup of `H x B`.  The reduced group C-star
inclusion is unital and faithful, so black-hole absorption makes
`C*_r(H x B)` invisible to every MF C-star target.
