---
rg: 2
id: clopen-crossed-product-subrings-have-local-annihilation-proof
kind: route
title: Separate a small clopen and its finitely many translates from a clopen W, and let χ_W annihilate
target: clopen-crossed-product-subrings-have-local-annihilation
requires: []
---

Let `F ⊆ R` be finite. Each `f ∈ F` is a finite sum `Σ_(γ ∈ Φ_f) g_(f,γ) u_γ`. Let `Φ` be the
finite set `{1} ∪ ⋃_f Φ_f ⊆ Γ`.

**Step 1: local choice.** Fix `x ∈ X`.
- `X` is infinite, so there is `y ∉ Φx = {γx : γ ∈ Φ}`, which is a finite set.
- The points `γ^-1 y`, `γ ∈ Φ`, all differ from `x`. So `X` Hausdorff and totally disconnected
  gives a clopen `V ∋ x` that contains none of them. Then `y ∉ γV` for all `γ ∈ Φ`.
- The set `V ∪ ⋃_(γ∈Φ) γV` is clopen and misses `y`. So its complement contains a clopen
  `W ∋ y`, and `W ≠ ∅`.

**Step 2: annihilation.** Let `t = χ_W ∈ R`, so `t ≠ 0`, and let `s ∈ χ_V R`.
- `ts = χ_W χ_V s = 0`, since `W ∩ V = ∅`.
- For `f ∈ F`, each term of `t f s` is
  `χ_W g_(f,γ) u_γ χ_V (...) = g_(f,γ) χ_(W ∩ γV) u_γ (...) = 0`,
  using `u_γ χ_V = χ_(γV) u_γ` and commutativity of `C(X, k)`.

So `χ_V R` lies in the set `S_F` of the definition.

**Step 3: partition.** By compactness finitely many of the `V`'s from Step 1 cover `X`. Refine them
to a clopen partition `V_1..V_r`, each `V_i` inside some `V(x_i)`. The same `W(x_i)` works for
`V_i`, because `V_i ∪ ΦV_i ⊆ V(x_i) ∪ ΦV(x_i)`. Hence `χ_(V_i) R ⊆ S_F`, and
`R = Σ_i χ_(V_i) R` lies in the additive span of `S_F`. ∎

**Model test.** If `X` is finite, Step 1 fails: take `Φx = X`, which holds for a transitive
action. This matches the field model test of `steinberg-algebras-have-local-annihilation`.
