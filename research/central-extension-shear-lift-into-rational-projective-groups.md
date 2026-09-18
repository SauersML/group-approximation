---
rg: 2
id: central-extension-shear-lift-into-rational-projective-groups
kind: claim
title: Shear lift - a central Z-extension of a subgroup of the rational projective full group T_m whose class dies on its action groupoid embeds in T_(m+2), with the centre acting as an integral shear
distinct_from:
  odometer-lift-central-extensions-of-v-subgroups-into-2v-tau: that realizes the centre by an adjoined odometer in a Katsura-type host; this realizes it inside the rational projective full group itself, by a unipotent integral shear in two extra coordinates, so no new host is needed.
  closed-mcg-embeds-in-rational-projective-full-group: that constructs T_m and embeds closed-surface mapping class groups; this is a permanence lemma for T_m under groupoid-trivial central extensions.
  deligne-class-dies-on-some-rational-projective-host: that is the open input needed to apply this lemma to Deligne's lattice.
---

**ESTABLISHED** (lane proof, elementary, not reviewed). No priority claimed.

## Setting

`𝒯_m = [[GL_{m+1}(Z) ⋉ Ŝ_m]]` on the rational Cantorization `Ŝ_m` of the ray sphere
`S^m`, as in `closed-mcg-embeds-in-rational-projective-full-group`. Clopen subsets of
`Ŝ_m` are the rational polyhedral regular open sets `B_m`. In `R^{m+3}` use
coordinates `(s, t, v)` with `v ∈ R^{m+1}`. `H_s` is the clopen of `Ŝ_{m+2}` given by
the rational half-sphere `{s > 0}`.
- **Pullback.** For `C ∈ B_m` put `P_C = int cl{[s,t,v] : s > 0, v ≠ 0, [v] ∈ C}`.
  It lies in `B_{m+2}`, since it is the same Boolean combination of `H_s` and the
  `H_{ℓ(v)}`. `C ↦ P_C` is a Boolean homomorphism `B_m → B_{m+2}|_{H_s}`, so it carries
  finite partitions of `Ŝ_m` to finite partitions of `H_s`.
- **Linear maps.** For `g ∈ GL_{m+1}(Z)` and `k ∈ Z`,
  `A_{k,g}(s,t,v) = (s, t + ks, gv)` lies in `GL_{m+3}(Z)` and maps `P_C` onto `P_{gC}`.

## Statement

Let `Q ≤ 𝒯_m` and let `1 → ⟨z⟩ → Q̃ → Q → 1` be a central extension, with `z` of
infinite order. Suppose `Q̃` acts on `Z × Ŝ_m` by

    q̃·(j, y) = (j + k(q̃, y), q y),     z·(j, y) = (j + d, y),   d ≥ 1,

with each `k(q̃, ·)` locally constant. That is, the class dies on `Q ⋉ Ŝ_m` (see
`groupoid-lifts-of-central-extensions-need-no-invariant-measure`). For `q̃ ∈ Q̃`,
choose a finite clopen partition `(C_i)` of `Ŝ_m` on which `k(q̃,·) ≡ k_i` and `q`
agrees with `g_i ∈ GL_{m+1}(Z)`. Define `Ψ(q̃)` to be `A_{k_i, g_i}` on `P_{C_i}`, and
the identity off `H_s`.

Then `Ψ : Q̃ → 𝒯_{m+2}` is an injective homomorphism, and `Ψ(z)` is the shear
`(s,t,v) ↦ (s, t + ds, v)` on `H_s`.

## Proof

- **In the full group.** `Ψ(q̃)` agrees on the pieces of the finite clopen partition
  `{P_{C_i}} ∪ {Ŝ_{m+2} ∖ H_s}` with elements of `GL_{m+3}(Z)`. The images
  `P_{g_iC_i} = P_{q C_i}` again partition `H_s`, since `(qC_i)` partitions `Ŝ_m`. So
  `Ψ(q̃)` is a homeomorphism in `𝒯_{m+2}`, independent of the partition chosen.
- **Homomorphism.** On a common refinement,
  `A_{k(q̃_1, q_2y), g_1} A_{k(q̃_2,y), g_2} = A_{k(q̃_2,y) + k(q̃_1,q_2y), g_1g_2}`, and
  `k(q̃_2,y) + k(q̃_1,q_2y) = k(q̃_1q̃_2, y)` by the action law.
- **Injective.** Suppose `Ψ(q̃) = id`. The points of `H_s` over rays with `[v]` in
  the dense set where `Ŝ_m → S^m` is injective show that `q` acts trivially on
  `Ŝ_m`, so `q = 1`. Then `q̃ = z^j`, and `Ψ(z^j)` is the shear by `jd`, so `j = 0`. ∎

## Consequence

If `j : Sp_{2n}(Z) ↪ 𝒯_m` is an embedding for which Deligne's class dies on the
action groupoid (`deligne-class-dies-on-some-rational-projective-host`), then
Deligne's lattice embeds in `𝒯_{m+2}`. If moreover `𝒯_{m+2}` is finitely presented
(`rational-projective-full-groups-are-finitely-presented`), then Deligne's lattice
satisfies Boone–Higman, since `𝒯_{m+2}` is full and clopen transitive
(`fp-clopen-transitive-full-cantor-groups-have-type-a-actions`). This is route
`deligne-bh-via-rational-projective-full-group`. The Deligne and closed
mapping-class-group routes then rest on the same finiteness statement.
