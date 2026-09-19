---
rg: 2
id: free-action-fg-alternating-full-groups-force-expansivity-proof
kind: route
title: Code points by the cells of the generators' cocycle partition; two points with the same code are moved by every word through the same group element, and a 3-cycle that moves one and fixes the other contradicts freeness
target: free-action-fg-alternating-full-groups-force-expansivity
requires: []
---

Notation as in the target. Group elements act on the left; `e` is the identity of `Λ`.

**Cocycles.** Freeness makes cocycles unique. For `g ∈ [[Λ ~ X]]` there is exactly one map `c_g : X → Λ` with
`g(x) = c_g(x)·x`, and `c_g` is locally constant, by the definition of the full group. So `c_g` takes finitely many
values, each on a clopen set.

**The partition.** Let `Γ = ⟨g_1, …, g_k⟩` contain every 3-cycle. Let `P` be the common refinement of the level sets of
the `2k` maps `c_{g_i}` and `c_{g_i^{-1}}`; it is a finite clopen partition. Put `π(x)(ν) =` the cell of `P`
containing `ν·x`, for `ν ∈ Λ`.

**Step 1 (equivariance).** `π(μ·x)(ν) = π(x)(νμ)`. So `(μ⋆z)(ν) := z(νμ)` is an action of `Λ` on `P^Λ` with
`π(μ·x) = μ⋆π(x)`. In particular `π(x) = π(y)` implies `π(μ·x) = π(μ·y)` for every `μ ∈ Λ`. Each coordinate of `π`
is locally constant, so `π` is continuous.

**Step 2 (same code, same displacement).** Suppose `π(x) = π(y)`. Then for every `g ∈ Γ` there is `ν ∈ Λ` with
`g(x) = ν·x` and `g(y) = ν·y`.
- Write `g = s_m ⋯ s_1` with each `s_j ∈ {g_i^{±1}}`, and put `x_j = s_j ⋯ s_1(x)`, `y_j = s_j ⋯ s_1(y)`.
- Induction on `j`, with `x_j = ν_j·x` and `y_j = ν_j·y`. The base is `ν_0 = e`.
- Step: by Step 1, `π(x_{j-1}) = π(y_{j-1})`. Reading coordinate `e`, the points `x_{j-1}` and `y_{j-1}` lie in the
  same cell of `P`. So `c_{s_j}(x_{j-1}) = c_{s_j}(y_{j-1}) =: a`, and `ν_j = a ν_{j-1}` works for both points.

**Step 3 (a separating 3-cycle).** Suppose `x ≠ y` and `π(x) = π(y)`.
- By freeness at most one `μ ∈ Λ` has `μ·x = y`. Since `|Λ| ≥ 4`, choose distinct `λ, λ' ∈ Λ \ {e, μ}`.
- Then `x, λx, λ'x` are pairwise distinct (freeness), and none of them is `y`.
- Choose a clopen `U ∋ x` so small that `U`, `λU`, `λ'U` are pairwise disjoint and `y ∉ U ∪ λU ∪ λ'U`.
- Let `t_1` exchange `U` and `λU` (by `z ↦ λz` on `U` and `z ↦ λ^{-1}z` on `λU`, the identity elsewhere). Let `t_2`
  exchange `U` and `λ'U` in the same way. Both lie in `[[Λ ~ X]]` and are involutions.
- So `g := [t_1, t_2] = (t_1 t_2)^2`. Tracking the point: `t_1t_2(x) = λ'x` and `t_1t_2(λ'x) = λx`, so `g(x) = λx ≠ x`.
  The element `t_1t_2` cycles `U → λ'U → λU → U` and has order 3, so `g = (t_1t_2)^{-1}` is a 3-cycle. Hence `g ∈ Γ`.
  (It also lies in `D([[Λ ~ X]])`, being a commutator.)
- `g` fixes `y`, which lies outside `U ∪ λU ∪ λ'U`.
- By Step 2 there is `ν` with `g(x) = ν·x` and `g(y) = ν·y`. From `g(y) = y` and freeness, `ν = e`, so `g(x) = x`.
  That is a contradiction.

**Conclusion.** `π` is injective, continuous and equivariant (Step 1), and `X` is compact. So `π` is a conjugacy of
`Λ ~ X` onto the closed invariant set `π(X) ⊆ P^Λ`, a subshift. Equivalently, the translates of the single partition `P`
separate points: the action is expansive. This proves item 1.

**Item 2.** Each of `[[Λ ~ X]]`, `D([[Λ ~ X]])` and `A([[Λ ~ X]])` contains every 3-cycle: `D` does by the commutator
identity in Step 3, and `A` by definition. Apply item 1 to each, if it were finitely generated.

**Item 3.** One direction is item 2. The other is Nekrashevych's theorem, quoted in the target. ∎

**What is used.** Only freeness and `|Λ| ≥ 4`. Minimality, amenability and finite generation of `Λ` are not used in
items 1 and 2.
