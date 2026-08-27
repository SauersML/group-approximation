---
rg: 2
id: invisible-quotient-grothendieck-comparison-proof
kind: route
title: Compare the two settings and locate the free end of the theorem
target: invisible-quotient-is-not-a-grothendieck-pair
requires:
  - compression-wreath-five-radicals-coincide
  - grothendieck-profinite-representation-equivalence
artifacts:
  - research/artifacts/invisible-quotients-architecture-audit-2026-08-23.md
---

Clause 1 is a comparison of definitions against the two prerequisites: the
imported notion requires an injection of residually finite groups, and the
computed radical shows `Res_fin(W_K) = R_K` is nontrivial, so `W_K` is not
residually finite and `q` is not an injection.

Clause 2.  Every homomorphism from `W_K` to a finite group has kernel
containing `Res_fin(W_K) = R_K`, by definition of the finite residual, hence
factors uniquely through `W_K/R_K = P_K`; and a homomorphism `P_K -> F` pulls
back.  So `q*` is a bijection on `Hom(-, F)` for finite `F`, compatibly with
the finite quotient maps, giving `W_K^ = P_K^`.  The only input is the value of
`Res_fin`, which the first prerequisite supplies.

Clause 3.  The universal inclusions: a finite group embeds in some `U(d)`, so
`Rad_fd  subset  Res_fin`; a finite group is MF and `U(d)` is MF, so
`Rad_MF  subset  Rad_fd`; and a finitely generated linear image is residually
finite by Malcev, hence MF, so `Rad_MF  subset  Rad_lin  subset  Res_fin`.  The
first prerequisite asserts equality throughout, which is exactly the collapse
of this chain.

**The Bohr column is the one clause that is not free here.**
`bohrResidual <= finiteResidual` is unconditional -- a finite group with the
discrete topology is compact Hausdorff.  The converse for general compact
targets is what Peter--Weyl supplies classically, but in this repository it is
an isolated named hypothesis, not a background fact: `five_radicals_eq` in
`Sofic/FiveRadicalsCoincide.lean` carries a leading binder
`(hPW : SeparatesPoints)`, and the unconditional companion
`five_radicals_eq_profinite` restricts the targets to profinite ones, where
`bohr-residual-equals-finite-residual-for-profinite-targets` closes the gap
with no analysis.  So the collapse is unconditional for the finite,
finite-dimensional-unitary, all-fields-linear and MF columns, and conditional
on that one classical input for the compact column.
