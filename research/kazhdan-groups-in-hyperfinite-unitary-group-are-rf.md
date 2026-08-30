---
rg: 2
id: kazhdan-groups-in-hyperfinite-unitary-group-are-rf
kind: claim
title: A finitely generated Kazhdan subgroup of U(R) is residually finite
invalidates: [non-mf-unitary-subgroup-via-kazhdan-non-mf-groups]
distinct_from:
  rank-twelve-leavitt-group-lacks-factorization-property: that is Kirchberg's theorem applied to the simple Kazhdan group H (factorization property would make it residually finite); this is the same rigidity read on the inside of U(R): a Kazhdan group with a faithful hyperfinite character is residually finite, so no Kazhdan non-MF group can witness non-quasidiagonality of R.
  hyperfinite-factor-qd-forces-unitary-subgroups-mf: that is the reduction of X(2) to unitary subgroups; this is the obstruction that removes the Kazhdan non-MF groups from the list of candidate witnesses.
artifacts:
  - research/artifacts/stw99-x2-unitary-subgroup-reduction-2026-08-30.md
---

Let `Γ` be a finitely generated group with Kazhdan's property (T) and let
`ρ : Γ → U(R)` be an injective homomorphism into the unitary group of the
hyperfinite II₁ factor (or of any hyperfinite finite von Neumann algebra
with faithful normal trace).  Then `Γ` is residually finite.

So every finitely generated Kazhdan subgroup of `U(R)` is residually finite,
hence MF.  In particular the simple Kazhdan non-MF group
`H = EL_12(L_{F_2}(1,2))` and the torsion-free finitely presented Kazhdan
group `Q` of `non_mf_groups_exist.tex` do not embed in `U(R)`, and cannot
serve as witnesses for `non-mf-subgroup-of-hyperfinite-factor-unitary-group`.

The argument does not touch non-Kazhdan groups: the literal group `E`
contains the Kazhdan base `Z^3 ⋊ SL_3(Z)`, which is residually finite, so
the obstruction is silent on `E`
(`literal-group-embeds-in-hyperfinite-unitary-group`).
