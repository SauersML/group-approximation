---
rg: 2
id: self-similar-tiling-full-groups-abelian-obstructions-vanish
kind: claim
title: Derived full groups of free minimal recognizable self-similar Z^2-subshifts have finitely generated homology in every degree, so no abelian obstruction can prevent their finite presentation
distinct_from:
  labbe-shift-derived-full-group-homology-is-finitely-generated: That is the instance for Labbé's 19-tile shift; this is the class statement for every free minimal Z^2-subshift carrying a recognizable expansive self-similar morphism.
  recognizable-self-similar-z2-subshifts-have-finite-cohomology: That bounds the mod-m cohomology of the base system; this converts that bound into finitely generated homology of the derived full group in every degree, and to the vanishing of additive relation obstructions.
artifacts:
  - research/artifacts/full-group-homology-fp-obstruction-labbe-2026-09-13.md
  - research/artifacts/full-group-homology-fp-obstruction-2026-09-13.md
---

**ESTABLISHED (unreviewed).**

**Setting.** `X ⊆ A^{Z^2}` is a subshift such that:
- `Z^2` acts freely and minimally on `X` (so `X` is a Cantor set);
- there is an expansive 2-dimensional morphism `ω : X -> X`, recognizable in `X`, with
  `X = closure_σ(ω(X))` (Labbé's sense, arXiv:1802.03265).

Put `Gamma = D([[Z^2 ~ X]])`, the finitely generated infinite simple derived full group
(`minimal-z2-subshift-derived-full-groups-are-fg-simple`).

**Theorem.**
1. `H_2(Gamma; Z) ≅ Z ⊕ T` with `T` a finite abelian 2-group of exponent at most 4.
2. `H_j(Gamma; Z)` is finitely generated for every `j`.
3. Every conjugation-invariant homomorphism from the relation subgroup `N` (of a free group on a
   finite generating set) to an abelian group has finitely generated image. In particular the
   mean signed area of relator loops against the invariant measure, and every additive
   invariant-measure "relation compression" invariant, does.

**Consequence.** For every group in this class, finite presentation cannot be refuted by:
- showing some homology group with trivial or finite coefficients is infinitely generated;
- exhibiting an additive relation invariant of unbounded rank.

So a refutation must be nonabelian. The surviving candidate on record is LEF
(`labbe-not-fp-via-lef` for the Labbé instance).

**Membership.** Labbé's 19-tile Wang shift `Omega_U` is in the class (Labbé's Proposition
`prop:pre-main`). Every primitive recognizable self-similar aperiodic Wang shift with a free
minimal hull qualifies. The Penrose group is treated separately, through Li's Penrose groupoid
homology, in `penrose-derived-full-group-homology-is-finitely-generated`, because it acts through
`Z^2 ⊕ Z/5` rather than as a `Z^2`-subshift.

**What this does not claim.** It does not address `FP_2`, which needs the relation module finitely
generated as a `Z[Gamma]`-module (homology with `Z[Gamma]` coefficients). Li's theorem reaches only
coefficients pulled back from abelian covers, so it says nothing about that. Finite presentation
of any member of the class stays open.

Proof: `self-similar-tiling-full-groups-abelian-immunity-proof`.
