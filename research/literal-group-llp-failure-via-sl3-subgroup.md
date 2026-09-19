---
rg: 2
id: literal-group-llp-failure-via-sl3-subgroup
kind: route
title: Restrict LLP to the embedded SL3 lattice
target: literal-group-fails-local-lifting-property
requires: [literal-telescope-split-normal-form]
artifacts:
  - GroupApproximation/Analysis/NuclearityBaseEmbedding.lean
  - notes/LITERAL_GROUP_BLOCK_AMALGAM_STRUCTURE_2026-08-14.md
---

The prerequisite identifies the telescope complement of the lamp kernel as

```text
V = (Z[1/2]^3 semidirect_product SL_3(Z)) semidirect_product Z
```

and gives a splitting `E = N_E semidirect_product V`.  The canonical copies
in these two semidirect products therefore give an injective homomorphism

```text
SL_3(Z) -> V -> E.                                             (ELR1)
```

(Equivalently, the level-zero embedding is certified directly by
`NuclearityBaseEmbedding.baseMap_injective`.)

Ioana--Spaas--Wiersma, *Cohomological obstructions to lifting properties for
full group C*-algebras of property (T) groups*, arXiv:2006.01874v2,
Corollary B, prove

```text
C*(SL_n(Z)) does not have LLP for every n >= 3.                 (ELR2)
```

Their Remark 1.2 records the canonical inclusion and conditional expectation
for `Sigma < Gamma` and concludes that LLP of `C*(Gamma)` implies LLP of
`C*(Sigma)`.  Apply this to `(ELR1)`.  If `C*(E)` had LLP, then
`C*(SL_3(Z))` would have LLP, contradicting `(ELR2)`.  Therefore `C*(E)`
fails LLP.
