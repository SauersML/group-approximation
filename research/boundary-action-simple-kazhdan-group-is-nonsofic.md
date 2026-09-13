---
rg: 2
id: boundary-action-simple-kazhdan-group-is-nonsofic
kind: claim
title: Over a finite field the boundary mirror of the Pestov group, EL_N(LC(∂F_d,k) ⋊ F_d) mod centre, is nonsofic
distinct_from:
  halvable-corner-makes-projective-elementary-groups-nonsofic: that is the general theorem that a halvable corner makes every quotient of EL_(nd)(R) by central scalars nonsofic, and this claim is a special case of it, since R_∂ has a halvable idempotent; what is new here is only the explicit boundary Leavitt family, so the ring hypothesis is verified by hand.
  boundary-action-elementary-simple-kazhdan-not-mf: that shows the same group has no nontrivial MF quotient; this shows it is not even sofic, via a unital Leavitt family and the Lean nonsoficity theorem.
  purely-infinite-simple-algebras-have-nonsofic-el-groups: that covers unit, GL and EL groups of purely infinite simple algebras; this covers the projective quotients EL_N/C for central scalar C, for the explicit boundary ring, with no Ara–Goodearl–Pardo input.
---

Let `k` be a finite field, `d >= 2`, `R_∂ = LC(∂F_d, k) ⋊ F_d` and `N >= 2`. For every subgroup
`C ≤ EL_N(R_∂) ∩ k^x I_N`, the group `EL_N(R_∂)/C` contains an isomorphic copy of `EL_N(R_∂)` and is nonsofic.

In particular, for `N >= 3`, `S_∂ = EL_N(R_∂)/Z(EL_N(R_∂))` is nonsofic. With
`boundary-action-elementary-simple-kazhdan-not-mf`, `S_∂` is an infinite, finitely generated, simple Kazhdan group
that is nonsofic and has no nontrivial MF quotient.

The mirror is sharp. The Pestov group `EL_3(LC(X,F_q) ⋊ Z)/Z` is LEF, hence sofic. The same construction over the
paradoxical boundary action lands on the other side of both lines.

ESTABLISHED by `boundary-action-simple-kazhdan-group-is-nonsofic-proof` (unreviewed).

**Review (un-verify-3, 2026-09-13): PASS.** The explicit family is re-derived in `boundary-crossed-product-carries-leavitt-family`. The corner copy `ψ = Φ∘EL_N(θ)` is re-derived: `θ(x) = s_1 x t_1` is a unital ring isomorphism `R_∂ → eR_∂e`; `Φ(X) = X + (1−e)I_N`; `ψ(X) = λI` forces `λ = 1`. It meets the central scalars trivially, so every `EL_N(R_∂)/C` is nonsofic, and so is `S_∂` for `N ≥ 3` by the reviewed scalar-centre theorem.
- **Lean backing.** The d-ary theorem is `GroupApproximation.CompleteMatrixFamily.elementary_not_isSofic` (`Leavitt/AryEndpoints.lean`, root-imported at `GroupApproximation.lean:702`; no placeholder tokens). Its `CompleteMatrixFamily` fields `right i * left j = δ_ij`, `Σ left i * right i = 1` match `t_i s_j = δ_ij`, `Σ s_i t_i = 1`. `IsSofic` is the standard Hamming definition. `#print axioms` on MSI gives `[propext, Classical.choice, Quot.sound]` for it and for the binary `FamilyRankFour.elementary_not_isSofic`.
- **Display slip (fixed by the owner lane).** The route named `LeavittFamily.elementary_not_isSofic`; the d-ary declaration is `CompleteMatrixFamily.elementary_not_isSofic`.
- **Subsumption.** This is a special case of `halvable-corner-makes-projective-elementary-groups-nonsofic` (established): `R_∂` has a halvable idempotent. It is also a case of `purely-infinite-simple-projective-el-groups-stable-nonsofic` once `R_∂` is known purely infinite simple. What is new here is only the explicit boundary family.
`research/artifacts/un-review3-2026-09-13-part2.md` §6.
