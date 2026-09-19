---
rg: 2
id: literal-telescope-core-lef-proof
kind: route
title: Finite block windows give residually finite level models
target: literal-telescope-core-lef
requires: [literal-telescope-split-normal-form, literal-lamp-kernel-clifford-block-amalgam, finite-telescope-level-coset-orbits]
artifacts:
  - notes/LITERAL_GROUP_IS_SOFIC_2026-08-14.md
  - GroupApproximation/Sofic/MappingTelescopeFiniteOrbits.lean
  - GroupApproximation/Sofic/SoficDirectedUnion.lean
  - GroupApproximation/Sofic/LEFSofic.lean
---

## Direct proof

Sections 3-4 of `notes/LITERAL_GROUP_IS_SOFIC_2026-08-14.md`.  A finitely
generated subgroup of `E_T` has all its telescope coordinates in one level
`Gamma_n` (the levels increase to `T`) and all its lamp coordinates in
finitely many blocks `J_0`.  Level orbits on the block set are finite, so
`J = Gamma_n J_0` is finite and invariant, and the subgroup lies in
`M_J semidirect Gamma_n`.

`M_J` is the amalgam of `|J|` copies of the order-512 Clifford lamp group over
their common central involution, so it is finitely generated and acts on its
Bass-Serre tree with finite vertex stabilizers, hence is virtually free and
residually finite.  The action of `Gamma_n` on `M_J` permutes the `8|J|` site
involutions and fixes the centre, so it factors through a finite symmetric
group; its kernel `Lambda` has finite index and centralizes `M_J`, giving
`M_J x Lambda` of finite index in `M_J semidirect Gamma_n`.  `Lambda` is
linear, hence residually finite (Mal'cev), so that direct product is
residually finite and so is the finite-index overgroup.  Subgroups of
residually finite groups are residually finite, so every finitely generated
subgroup of `E_T` is residually finite; that is exactly local embeddability
into finite groups, which gives soficity and MF.

Splitness is used and is available: the extension `M_J semidirect Gamma_n` is
split.  The route does NOT use the false statement that
finite-by-residually-finite extensions are residually finite (Deligne).
