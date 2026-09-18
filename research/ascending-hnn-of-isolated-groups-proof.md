---
rg: 2
id: ascending-hnn-of-isolated-groups-proof
kind: route
title: Discriminate products through centres and commutators, wreath with S_k by the centralizer of the base, and split ascending HNN extensions by whether something outside the base centralizes it
target: ascending-hnn-of-isolated-groups-embed-in-isolated-groups
requires:
  - fp-simple-groups-are-isolated
---

Throughout, `F_J` denotes a finite discriminating set of `J`.

**0. Centres.** If `J` is finitely discriminable, then `Z(J)` is torsion with finite socle.
- An element `z ∈ Z(J)` of infinite order gives normal subgroups `<z^n>` whose intersection is
  trivial, and one of them misses `F_J`. So `Z(J)` is torsion.
- Every subgroup of order `p` in `Z(J)` is normal, so it contains some `f ∈ F_J`, and it equals
  `<f>`. So there are at most `|F_J|` such subgroups, and the socle is finite.

**1. Products.** Let `1 ≠ (x, y) ∈ N ⊴ J_1 × J_2`.
- If `x ∉ Z(J_1)`, pick `g` with `[x, g] ≠ 1`. Then `([x,g], 1) ∈ N ∩ (J_1 × 1)`, which is
  normal in `J_1`, so it meets `F_1 × 1`. The case `y ∉ Z(J_2)` is symmetric.
- Otherwise `(x, y) ∈ Z(J_1) × Z(J_2)`, which is torsion by step 0. A suitable power of
  `(x, y)` has prime order, so it lies in the socle `Ω` of `Z(J_1) × Z(J_2)`. `Ω` is finite by
  step 0.

So `(F_1 × 1) ∪ (1 × F_2) ∪ (Ω − 1)` discriminates. Finite presentation of the product is
clear.

**2. `J ≀ S_k`.** Let `1 ≠ N ⊴ J^k ⋊ S_k`, with `J ≠ 1`. If `N ∩ J^k = 1`, then
`[N, J^k] ⊆ N ∩ J^k = 1`. Let `(x, σ) ∈ N` with `σ(i) = j ≠ i`. It conjugates a nontrivial
element in coordinate `i` into coordinate `j`, so it does not centralize `J^k`. So `σ = 1`
and `N ⊆ J^k`, a contradiction. Hence `N ∩ J^k` is a nontrivial normal subgroup of `J^k`
and meets `F_{J^k}` (step 1). Finite presentation is clear.

For the closure statement: by Kaloujnine--Krasner, `G' <= G ≀ S_k <= J ≀ S_k` whenever
`G <= J` has index `k` in `G'`.

**3. Ascending HNN.** `I ⊆ t^-1 I t`, since `t I t^-1 = α(I) ⊆ I`. So `B` is an increasing
union, normal, and `Γ/B ≅ Z`. Let `1 ≠ N ⊴ Γ`.
- If `N ∩ B ≠ 1`, pick `1 ≠ x ∈ N ∩ t^-m I t^m`. Then `t^m x t^-m ∈ N ∩ I` is nontrivial, so
  `N ∩ I` meets `F_I`.
- If `N ∩ B = 1`, then `N` embeds in `Γ/B ≅ Z`, so `N = <c>` with `c = y t^k`, `y ∈ B`,
  `k >= 1` (after inverting). Also `[N, B] ⊆ N ∩ B = 1`.

So in case (A), `F_I` discriminates `Γ`. `Γ` is finitely presented by the finite presentation
of `I` plus `t x_i t^-1 = α(x_i)`.

**Case (B).** Let `c = y t^k` centralize `B`, with `y ∈ I_m := t^-m I t^m`.
- For `x ∈ I` we get `t^-k x t^k = c^-1 y x y^-1 c = y x y^-1`, since `yxy^-1 ∈ B`
  commutes with `c`. By induction `I_(jk) = y^j I y^-j ⊆ I_m` for all `j >= 0`, because
  `y ∈ I_m` and `I ⊆ I_m`.
- So `B = ⋃_j I_(jk) = I_m ≅ I`. Then `<c> ∩ B = 1`, `c` centralizes `B`, and `B<c>` has
  index `k`, since its image in `Γ/B` is `kZ`.
- So `Γ` is a finite extension of `B × Z ≅ I × Z <= I × V`. That group is isolated by step 1
  and `fp-simple-groups-are-isolated`. Step 2 gives `Γ ∈ 𝓘`.

**4. Criterion.** `g ↦ (f(g), gN)` is injective when `f` is injective on `N`. Its target
embeds in `I × J` with `J` isolated, `G/N <= J`. ∎

The consequences in the target are direct applications. The Kurosh remark: for `β ∈ Aut(S * F_m)`
with `S` simple and not cyclic, `β(S)` is a conjugate `gSg^-1`. In `S * F_m`, `gSg^-1 ∩ S = 1`
unless `g ∈ S`. So `β(S) ⊆ S` forces `β(S) = S`.
