---
rg: 2
id: degree-category-comparison-type-a-proof
kind: route
title: Units do not change cylinders, the Cuntz colour lets one duplicate a cylinder before refining it, and strong connectivity then spreads any clopen set over its whole piece
target: degree-category-full-groups-stabilized-have-type-a-actions
requires: [stabilized-kgraph-full-group-clopen-action-proof, type-a-action-gives-boone-higman-for-subgroups, boone-higman-type-a-class-closed-under-finite-extensions]
---

Notation as in the target. Write `ℭ'' = ℭ x O_2`. For a morphism `λ`, the
cylinder `Z(λ) ⊆ ∂Ω(t(λ))` is a copy of `∂Ω(s(λ))` through `x ↦ λx`. For a unit `u`,
`Z(λu) = Z(λ)`.

**Step 1 (cylinder calculus).**
- Every clopen subset of `C''` is a finite disjoint union of cylinders, because
  cylinders form a basis of compact open sets, and intersections and differences of
  cylinders are finite disjoint unions of cylinders by (UFP*).
- For `s(λ) = w` and a colour `j`, the cylinders `Z(λμ)` partition `Z(λ)`, where `μ`
  runs over the morphisms of degree `ε_j` with target `w`, taken modulo units on the
  right (UFP*).
- Two cylinders with the same source are equivalent by the prefix replacement
  `λx ↦ λ'x`, which is the compact open bisection `λ'λ^(-1)` of `I_l ⋉ ∂Ω`.

**Step 2 (comparison, item 1).** Record a decomposition of a clopen set `U ⊆ C''_s` by
the number of cylinders with each source, a vector in `N^(V_s)`. Decompositions with
equal vectors give equivalent sets (Step 1). The moves:
- **(M1) Duplicate.** Refining `Z(λ)` in the Cuntz colour replaces it by `Z(λℓ_1)` and
  `Z(λℓ_2)`, which have the same source. So the count at `s(λ)` rises by one.
- **(M2) Spread.** First apply (M1) at `w = s(λ)`, then refine one of the two copies in
  a colour `j <= k`. The count at `w` stays at least one, and the sources of the
  degree-`ε_j` morphisms ending at `w` enter the support.
Iterating (M2) along the factors of a morphism puts every source of a morphism with
target in the support into the support. By strong connectivity of the piece, the
support becomes `V_s`, and (M1) then raises every count at will. So any two nonempty
clopen subsets of `C''_s` have decompositions with a common vector, and they are
equivalent. No loops in colours `1..k` are needed here.

**Steps 3–4 (items 2 and 3).** The pieces `C''_s` are clopen and invariant, so
`D = ∏_s F(𝒢''|_(C''_s))`, each factor a retract of `D`, hence finitely presented.
With item 1 in place of the refinement lemma, Steps 4 and 5 of
`stabilized-kgraph-full-group-clopen-action-proof` apply word for word:
- the action on clopen sets is faithful;
- there are finitely many orbits of pairs, recorded by which Boolean atoms meet which
  pieces;
- stabilizers are finite products of the finitely presented groups
  `F(𝒢''|_(C''_s))`;
- `D` is finitely presented by hypothesis.
So the action is of type (A), and `D ∈ B_A`. `F(𝒢|_Z)` embeds by `g ↦ g x id` (a
product of a bisection with a unit of `𝒢_(O_2)`), so it lies in `B_A` too, as do all
subgroups.
