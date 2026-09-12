---
rg: 2
id: dyadic-perturbation-group-mf-radical-is-finitary-alternating
kind: claim
title: The dyadic perturbation group is a sofic non-MF group whose MF radical is the finitary alternating group
distinct_from:
  affine-perfect-lamp-wreath-has-locally-finite-mf-radical: that is an ordinary wreath product whose radical is a restricted direct power of A_5, so not simple, and whose construction needs a lamp group and a finite-index self-embedding; this radical is the finitary alternating group, which is simple, and the group has no nontrivial finite normal subgroup at all.
  finitely-presented-sofic-non-mf: that is the finitely presented forty-one-relator group with a central involution in its radical; this group is only finitely generated, is torsion-full, and has an infinite simple MF radical.
  locally-finite-defect-subgroup-dies-in-every-corona: that is the unrestricted conjecture about any locally finite normal subgroup of the compression defect; this is one confirming instance, obtaining the criterion's commuting-conjugate relation from disjointness of supports, and does not prove the conjecture.
  literal-mf-radical-is-unsquared-defect: that computes the radical of the literal finitely presented group as the normal closure of an unsquared defect; this computes a different group's radical and identifies it with a finitary alternating group.
artifacts:
  - research/artifacts/dyadic-finite-perturbation-sofic-non-mf-2026-09-08.md
---

**ESTABLISHED.**  For the group `G` of
`dyadic-finite-perturbation-group-elementary-structure` and
`Gamma = Z^3 x| SL_3(Z) <= G`,

```text
D_G(Gamma) = Rad_MF(G) = Alt_fin(X),                              (DR1)
```
where `D_G(-)` is the intrinsic compression-centralizer defect.  In
particular:

* every norm-corona homomorphism of `G` kills every finitary even
  permutation of `X`, so `G` is **not MF**;
* `G / Rad_MF(G) = C_2 x H` is residually finite and MF;
* `Rad_MF(G)` is infinite, locally finite and **simple**.

Combined with `dyadic-perturbation-group-is-sofic` and
`dyadic-finite-perturbation-group-elementary-structure`, this gives a
finitely generated group that is sofic and not MF, has no nontrivial
finite normal subgroup, and is defined intrinsically as the finite
perturbations of one affine action.

**Scope.**  The analytic content is entirely
`locally-finite-centralizer-derived-subgroup-is-mf-invisible`, which is
consumed unchanged; nothing here is a property-(T)-free argument, and no
Lean certification is asserted.  This is a confirming instance of
`locally-finite-defect-subgroup-dies-in-every-corona` with `A` infinite,
locally finite, simple and equal to the whole defect — not a proof of it.

DERIVATION
dyadic-perturbation-radical-proof
