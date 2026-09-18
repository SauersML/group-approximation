---
rg: 2
id: annular-free-factor-germ-extensions-fail-bhm-singfix
kind: claim
title: In a finite germ extension of V whose germ group at 0^∞ has the zoom as a free factor, with the other factor preserving every cone 0^nC, the one-point SingFix group is not finitely presented; finite annular actions also exclude the ascending alternative
requires:
  - rf-groups-have-free-product-germs-over-v
distinct_from:
  rf-groups-have-free-product-germs-over-v: that builds hosts for every residually finite group with germ group G * Z; this shows the Belk--Hyde--Matucci Theorem 2.1 certificate cannot apply to them, and that the ascending alternative is closed to annular finite realizations.
  bhm-singfix-condition-forces-fp-germ-groups: that derives finite presentation of the germ group from finite presentation of SingFix({p},{p}); this shows the converse fails: here the germ group is finitely presented and SingFix({p},{p}) is not.
  orbit-preserving-germ-corollary-extensions-of-v-are-rational: that treats germ groups in which (V)_p is normal, where the host is rational; this treats germ groups in which (V)_p is a free factor.
---

**ESTABLISHED** by `annular-free-factor-singfix-colimit-proof` (lane proof, elementary
apart from the normal form theorem for amalgams; not reviewed; no priority claimed).

**Setting.** Notation of `rf-groups-have-free-product-germs-over-v`: `C`, `p = 0^∞`,
`A_n`, `α_n`, the zoom `τ` with germ `t`. `Γ` is a finite germ extension of `V` with
`p ∈ sing(Γ)`. Put `S_p = SingFix_Γ({p},{p})`, `K_p = RStab_V(p)`, and
`B_n = {v ∈ V : v = id on 0^n C}`, so `K_p = ⋃_n B_n`.

**Theorem.**
1. **Free factor.** Suppose some subgroup `Ĥ <= S_p` maps isomorphically onto its germs
   `H != 1`, with `(Γ)_p = <t> * H`, and every element of `Ĥ` maps each `0^n C` onto
   itself. Then `S_p` is not finitely presented. So Theorem 2.1 of Belk--Hyde--Matucci,
   which needs `S_p` of type `F_2` for finite presentation, does not apply to `Γ`. This
   covers every host of `rf-groups-have-free-product-germs-over-v`.
2. **No ascending alternative.** Let `G` be infinite and finitely generated, and let
   `g ↦ ĝ` be any faithful action fixing `p`, preserving every `A_n`, and acting on each
   `A_n` through a finite group `ρ_n(G)`, as in item 1 of that node. Then no injective
   `φ: G -> G` satisfies `t^(-1) (ĝ)_p t = (φ(g)^)_p` for all `g`. In particular
   `(Ĝ)_p` is not normalized by `t`.

**What this says.** For hosts of one singular orbit at `0^∞`, the relation between the
zoom and the germs of the input has three extreme shapes.
- *Normal:* the zoom normalizes, or is normalized by, the germs. Where `(V)_p` is normal,
  the host is rational (`orbit-preserving-germ-corollary-extensions-of-v-are-rational`),
  so hard inputs are excluded. Item 2 excludes `t`-invariance of the germs for finite
  annular inputs.
- *Free factor:* the zoom is free from the germs. The germ group is finitely presented,
  but `S_p` is not (item 1), because every depth carries new relations. The input acts on
  each deeper annulus through a finer finite quotient, and nothing transports them.
- *Ascending:* `t^(-1) G t <= G` on germs. Item 2 excludes this for finite annular
  inputs, because preimages of a finite-index subgroup under an endomorphism have
  bounded index.

What remains is `t^(-1) U t <= G` on germs for a finite-index `U <= G` only. That is a
virtual endomorphism, and the indices may then grow geometrically. So the one-point germ
route for Problem 5.3(12) leads back to the self-similar shape of
`fp-rf-boone-higman-via-fp-self-similar-overgroups`, now with a precise reason.
