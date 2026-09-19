---
rg: 2
id: non-amenable-stabilizer-from-gluing-a-cone-compactification
kind: route
title: Glue the cone compactification of F_2 × Z to C_Z along the Bass–Serre tree; the point whose sink piece carries the global fixed point is stabilized by F_2 × Z
target: rigid-minimal-topfree-sft-with-non-amenable-point-stabilizer
requires:
  - products-with-z-have-rigid-compactifications-with-fixed-points
  - tree-gluing-turns-rigid-sft-compactifications-into-rigid-sfts
---

Lane proof by bh-break, 2026-09-18. Not reviewed. Notation as in the tree-gluing node.

## 1. The input compactifications

- `C_Z` is a rigid compactification of `Z` (tree-gluing node, Basic members). By part 4 of the tree-gluing
  theorem with `Λ_0 = Λ_1 = Z`, `F_2 = Z * Z ∈ 𝒞` through some rigid compactification `(Y_F, π_F)`.
- By `products-with-z-have-rigid-compactifications-with-fixed-points`, `Γ = F_2 × Z` has a
  compactification `(Y, π)`, rigid over every field at all large scales, with a point `y_+ ∈ Y` fixed by
  all of `Γ`. Since `y_+` is fixed and `Stab(y_*) = 1`, `y_+` is seedless, so `y_+ ∈ ∂Y`.

## 2. The gluing

Apply the tree-gluing theorem to `Λ_0 = Γ` with `(Y, π)` and `Λ_1 = Z` with `C_Z`. Both are nontrivial
and not of order 2. The theorem gives an SFT `X` over `Λ = Γ * Z` that is minimal, topologically free,
and `D`-quantum rigid over every field for all large `D`. This is parts 1 and 2 of the target. `Λ` is
finitely presented since `Γ` and `Z` are.

## 3. The point x_∞

By Step A (Existence) of the tree-gluing proof, there is `x_∞ ∈ X` whose sink is the piece `P = Γ`
(the coset of the identity, of kind 0), with `x_∞|_P = y_+`, and every other piece seeded at its exit
toward `P`.
- **`Stab(x_∞) ⊆ Γ`.** A point of `X` has at most one sink piece (Step A, Consequence), and `g.x_∞` has
  sink `gP`. So `g.x_∞ = x_∞` forces `gP = P`, i.e. `g ∈ Γ`.
- **`Γ ⊆ Stab(x_∞)`.** For `g ∈ Γ`, the point `g.x_∞` has sink piece `gP = P` carrying
  `g.y_+ = y_+`. By Step A (Determination), every non-sink piece is seeded at its exit, and exits are
  determined by the tree and the sink. So `g.x_∞` and `x_∞` agree on every piece, and on both
  coordinates, hence are equal.

So `Stab(x_∞) = Γ = F_2 × Z`. This is part 3.

## 4. Non-amenability

**Fact (standard, recalled with proof).** If `Λ ↷ X` is topologically amenable, every point stabilizer
`H` is amenable.
- Take continuous `m_n : X → Prob(Λ)` with `sup_x ‖g.m_n(x) − m_n(g.x)‖_1 → 0` for every `g`.
- For `x` fixed by `H`, the measures `μ_n = m_n(x)` satisfy `‖h.μ_n − μ_n‖_1 → 0` for `h ∈ H`.
- Choose a right transversal `T` of `H` in `Λ`. The map `Λ → H`, `ht ↦ h`, is `H`-equivariant for left
  multiplication. Pushing `μ_n` forward gives a Reiter sequence on `H`, so `H` is amenable.

`F_2 × Z` contains `F_2`, so it is not amenable. Hence `Λ ↷ X` is not topologically amenable. `∎`

## 5. What is imported

- The tree-gluing theorem, parts 1–4, and its Step A. It is ESTABLISHED on main as a lane proof, not
  reviewed. This lane re-checked Steps A and D. Step D uses only the chain
  `1 − A_i ≤ B_i ≤ 1 − A_(i+1)` and rigidity of each vertex compactification, and does not care about
  boundary isotropy.
- The cone lemma, proved here from scratch.
