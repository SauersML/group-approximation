---
rg: 2
id: literal-telescope-core-lef-via-central-embedding
kind: route
title: The same window argument with the virtual-freeness step replaced by a central embedding
target: literal-telescope-core-lef
requires: [literal-telescope-split-normal-form, literal-lamp-kernel-clifford-block-amalgam, finite-telescope-level-coset-orbits, clifford-block-amalgam-residually-finite, literal-base-presentation-complete]
artifacts:
  - notes/E_SOFICITY_SELF_CONTAINED_2026-08-16.md
  - GroupApproximation/Sofic/MappingTelescopeFiniteOrbits.lean
  - GroupApproximation/Sofic/SoficDirectedUnion.lean
  - GroupApproximation/Sofic/LEFSofic.lean
---

## Why sufficient

Sections 9 and 10 of the artifact.  The window argument is the same one as in
`literal-telescope-core-lef-proof`, and only its two outside inputs change.

Let `H <= E_T` be finitely generated, `H = <h_1, ..., h_r>`.  Write
`h_j = p_j g_j` with `p_j` in the lamp kernel and `g_j` in `T`
(`literal-telescope-split-normal-form`).  The levels increase to `T`, so one
level `Gamma_n` contains every `g_j`.  Each `p_j` is a finite word in the block
amalgam (`literal-lamp-kernel-clifford-block-amalgam`), so a finite set `J_0`
of blocks carries all of them, and `J = Gamma_n · J_0` is finite
(`finite-telescope-level-coset-orbits`) and `Gamma_n`-invariant.  Hence
`H <= M_J semidirect Gamma_n`.

`Gamma_n` acts on `M_J` by permuting the `8|J|` site involutions and fixing the
centre, so the action factors through `Sym(sites(J))` and its kernel `Lambda`
has finite index in `Gamma_n` and centralizes `M_J`; therefore
`M_J x Lambda <= M_J semidirect Gamma_n` with finite index.  Both factors are
finitely generated and residually finite, so the product is, and residual
finiteness passes up to a finite-index overgroup of a finitely generated group
and back down to subgroups.  Every finitely generated subgroup of `E_T` is
residually finite, hence `E_T` is LEF, hence sofic and MF
(`lef-implies-operator-mf`).

## The two replaced inputs

* **`M_J` residually finite.**  The older route gets this from
  Karrass--Pietrowski--Solitar (input (S5) of
  `notes/LITERAL_GROUP_IS_SOFIC_2026-08-14.md`): `M_J` acts on the tree of a
  finite star of finite groups with finite vertex stabilizers, hence is
  virtually free.  Here it is the prerequisite
  `clifford-block-amalgam-residually-finite`, proved by the two-quotient
  embedding `M_J -> C(sites(J)) x (*_{i in J} (Z/2)^8)`, with no
  virtual-freeness theorem.
* **`Gamma_n` residually finite.**  The older route argues that `Gamma_n` is
  linear and quotes Mal'cev — and the 2026-08-15 audit flagged exactly this as
  the conditional step, since `Gamma_n` is a conjugate of the image of the
  PRESENTED base and linearity of that needs `B ~= Gammabar`.  With
  `literal-base-presentation-complete` the identification is a theorem, and
  then no Mal'cev is needed either: `Gamma_n ~= Z^3 semidirect SL_3(Z)` is
  separated by the congruence quotients
  `(Z/m)^3 semidirect SL_3(Z/m)` (Section 2, Lemma 2.1 of the artifact).

## Why the older route is kept

`literal-telescope-core-lef-proof` states the same window argument with fewer
prerequisites and is the historical record of how the claim was first
established; it is also the one whose phrasing the manuscript follows.  This
route is the one with no literature input.  Both are valid; they differ only
in what they consume.
