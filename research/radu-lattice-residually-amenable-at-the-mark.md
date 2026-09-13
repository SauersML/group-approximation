---
rg: 2
id: radu-lattice-residually-amenable-at-the-mark
kind: claim
title: The mark (xz)^4 of Radu's lattice survives in some amenable quotient
distinct_from:
  radu-bmw-lattice-sofic: that is soficity of Gamma_R; this is the stronger local-amenability input at one element, necessary for any residual-amenability proof of soficity.
  radu-mark-survives-only-in-non-rf-split-quotients: that constrains what such a quotient must look like; this asks whether one exists.
  radu-nilpotent-by-arithmetic-quotients-are-sofic: that asks for soficity of the free-nilpotent-by-arithmetic quotients G_k, which are not amenable; this asks for an amenable quotient.
refuted_by:
  - radu-mark-survives-only-if-horizontal-group-embeds
---

**REFUTED** (2026-09-13, unreviewed) by `radu-mark-survives-only-if-horizontal-group-embeds`.
The refuted statement: there is `N ◁ Γ_R` with `Γ_R/N` amenable and `(xz)^4 ∉ N`.

Why it matters. `Γ_R` is finitely presented, so it is locally embeddable into amenable groups
exactly when it is residually amenable. Residual amenability of `Γ_R` would make it sofic, and every
element outside the finite residual is already separated by finite quotients. So a residual-
amenability proof of `radu-bmw-lattice-sofic` needs this claim at the mark, and the analogous claim
at every element of the finite residual.

What any witness must look like (`radu-mark-survives-only-in-non-rf-split-quotients`, together with
`radu-arithmetic-quotient-normal-subgroups-finite-or-finite-index`):
* `Γ_R/N` is a finitely generated amenable group that is not residually finite;
* it is virtually `B = K/(N ∩ K)`, a non-abelian quotient of the free kernel `K`, and a
  finite-index subgroup `M = NK` of `Γ_R` satisfies `M/(N ∩ K) ≅ B × ρ(M)`;
* in `B` the root `δ^2` is conjugate to `δ^(−2)`, so `δ^4 ∈ [B,B]`.

Calibration.
* Cornulier's non-elementary-soficity criterion (arXiv:0906.3374, Proposition "nes": finitely
  presented, not residually finite, and hereditarily just infinite modulo a finite normal subgroup)
  does not apply to `Γ_R`: `K` is an infinite normal subgroup of infinite index. It does apply to the
  Titz–Witzel kernel containing `Γ_R` (`titz-witzel-kernel-not-elementary-sofic`), which is isolated,
  whereas `Γ_R` is a marked limit of the groups `Γ_R/γ_k(K)`.
* No candidate witness is known. Metabelian and, more generally, residually finite amenable quotients
  are excluded by item 1 of the structure claim.

Refutation (2026-09-13). Suppose `(xz)^4 ∉ N`. Then `N` meets no vertex stabilizer of the vertical tree
`T_v`. Otherwise a boundary vertex of the fixed tree of a kernel element puts `xz` into the image of
`<a,b,c>`, and Radu's Lemma 3.5 kills the mark. So `<a,b,c> ≅ C_2*C_2*C_2` embeds in `Γ_R/N`, and
`Γ_R/N` is not amenable. Consequences:
* `Γ_R` is not residually amenable and not LEA;
* the witness class described above is empty;
* residual amenability cannot certify `radu-bmw-lattice-sofic`.
