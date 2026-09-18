---
rg: 2
id: almost-v-torsion-localization-proof
kind: route
title: Singular sets obey a cocycle rule, the pointwise fixer of a finite singular orbit has germ map with kernel in V, and V is torsion locally finite
target: torsion-subgroups-of-almost-v-groups-localize-at-singular-germs
requires:
  - almost-automorphism-torsion-subgroups-are-rf
  - almost-v-fw-subgroups-act-through-finitely-many-germs
---

Notation as in the target. Two facts about `V` are recorded in `almost-v-fw-subgroups-act-through-finitely-many-germs`:
- **(F1) Fullness.** A homeomorphism of `C` that is locally in `V` at every point lies in `V`.
- **(F2) Cocycle rule.** `sing(fg) ⊆ sing(g) ∪ g^{-1}(sing f)` and `sing(g^{-1}) = g(sing g)`.

**(R)** `V` is torsion locally finite: `almost-automorphism-torsion-subgroups-are-rf`, item 2 (Röver's theorem).

## Item 1

Put `Σ_S = ⋃_{s ∈ S^{±1}} sing(s)`, a finite set. Write `t = s_1 ⋯ s_m` with `s_i ∈ S^{±1}`. Iterating (F2),

    sing(t) ⊆ ⋃_i (s_{i+1} ⋯ s_m)^{-1} sing(s_i) ⊆ T · Σ_S = Σ.

`Σ` is `T`-invariant by definition. ∎

## Item 2

`T` permutes the finite set `Σ`. So the pointwise fixer `T_1` is normal of finite index, and it is finitely generated.

For `y ∈ Σ`, taking germs at the fixed point `y` is a homomorphism `T_1 → 𝒢_y`. Let `t ∈ ker φ`:
- at each `y ∈ Σ` its germ is the identity germ, which is the germ of `1 ∈ V`;
- at points outside `Σ` it is `V`-local by item 1.

By (F1), `t ∈ V`. Conversely, elements of `T_1 ∩ V` have `V`-germs, possibly non-identity, at the points of `Σ`. So
`ker φ ⊆ T_1 ∩ V` (equality need not hold), and `ker φ` is a torsion subgroup of `V`, hence locally finite by (R).
Items (a)–(c) below use only `ker φ ⊆ V`.

- **(a)** Suppose every `[T_1]_y` is finite. Then `ker φ` has finite index in the finitely generated `T_1`, so it is
  finitely generated. Being a torsion subgroup of `V`, it is finite by (R). So `T_1` and `T` are finite.
- **(b)** `T_1 / ker φ` embeds in `∏_{y∈Σ} [T_1]_y`, and each factor is a quotient of `T_1`, hence finitely
  generated and torsion.
- **(c)** Let `T` be infinite and simple.
  - `T_1` is a normal subgroup of finite index, and `T` is infinite and simple, so `T_1 = T`: `T` fixes `Σ`
    pointwise.
  - `ker φ` is normal in `T`, so it is `1` or `T`. If it were `T`, then `T ≤ V` would be finitely generated torsion,
    hence finite by (R), a contradiction. So `φ` is injective.
  - Let `K_y` be the kernel of the `y`-coordinate. Each `K_y ∈ {1, T}`, and `⋂_y K_y = ker φ = 1`, so some
    `K_y = 1`. Then `T → [T]_y ⊆ (E)_y` is injective for every `E ≤ 𝐇` containing `T`. ∎

## Item 3

If `Σ` is finite and `T` is infinite, then by (a) some `[T_1]_y` is infinite. It is finitely generated and torsion by
(b). Otherwise `Σ` is infinite. ∎
