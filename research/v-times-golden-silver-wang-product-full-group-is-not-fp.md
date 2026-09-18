---
rg: 2
id: v-times-golden-silver-wang-product-full-group-is-not-fp
kind: claim
title: For the product of the golden and silver metallic mean Wang shifts, the full group of V times the Z^2 transformation groupoid is not finitely presented, so P2 is false
distinct_from:
  v-times-minimal-free-sft-alternating-full-groups-are-fp: that is the universal assertion P2 (every minimal free SFT over every infinite finitely presented group); this is one explicit pair (Z^2, Ω_1 × Ω_2) for which the conclusion fails, so it refutes P2.
  fp-v-times-subshift-full-groups-force-connected-differences: that is the necessary condition (coarse connectivity of difference sets); this applies it to a concrete minimal free SFT that violates it.
  labbe-wang-shift-crossed-product-is-finitely-presented: that asks for finite presentation of the crossed product of one Labbé shift; this is about the V-product full group of a product of two metallic mean shifts, and says nothing about a single Labbé shift.
  free-minimal-z2-sft-is-quantum-rigid: that is existential (some minimal free Z^2 SFT is quantum rigid); this exhibits one minimal free Z^2 SFT for which the V-product full group is not finitely presented, which is compatible with it.
  metallic-wang-shift-product-is-minimal-with-split-differences: that is the dynamical input (minimal, free, finite type, split differences); this is the group-theoretic conclusion.
---

**ESTABLISHED (unreviewed).** Route: `v-times-golden-silver-wang-product-full-group-is-not-fp-proof`.

**Setting.**
- `Λ = Z^2`, with generators `±e_1, ±e_2`. It is infinite and finitely presented.
- `X = Ω_1 × Ω_2 ⊆ (T_1 × T_2)^(Z^2)` is the product of Labbé's golden (`n = 1`) and silver
  (`n = 2`) metallic mean Wang shifts, with the diagonal shift action. This is the shift of
  `metallic-wang-shift-product-is-minimal-with-split-differences`.
- `G_V` is the groupoid of germs of Thompson's group `V` on `C = {0,1}^N`,
  `T = G_V × (Z^2 ⋉ X)`, and `t_s`, `e_a` are as in
  `fp-v-times-subshift-full-groups-force-connected-differences`.

**Theorem.**
1. No finitely presented subgroup `Γ ≤ F(T)` contains every `t_s` and every `e_a`.
2. In particular `A(T) = F(T)` is not finitely presented, although `X` is a nonempty subshift of
   finite type on which `Z^2` acts freely and minimally.
3. Hence premise P2 (`v-times-minimal-free-sft-alternating-full-groups-are-fp`) of
   `boone-higman-via-v-times-aperiodic-sft-full-groups` is false.

**Scope.**
- *What falls.* P2 as stated is universal over all pairs `(Λ, X)`. Any route that feeds an
  arbitrary minimal free SFT, for example one produced by P1
  (`decidable-groups-embed-in-fp-groups-with-minimal-free-sft`), into P2 loses that step.
- *What survives.* An existential or restricted P2 survives: finite presentation of `A(T)` for
  some minimal free SFT, or for SFTs whose difference sets are coarsely connected. By
  `fp-v-times-subshift-full-groups-force-connected-differences`, coarse connectivity (wall
  rigidity) is now a necessary hypothesis of any corrected P2. It is not implied by minimality,
  freeness, finite type, zero entropy, or the absence of finite asymptotic pairs.
- *Mechanism.* Each factor has a two-row fault along a horizontal partition line. The factors'
  eigenvalue groups are independent, so the faults can be translated apart without losing
  minimality. The basis-switching representation then separates two commuting site-conditioned
  3-cycles.
