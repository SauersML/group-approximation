---
rg: 2
id: identity-edge-extensions-over-pair-stabilizers-lie-in-b-a
kind: claim
title: An identity-edge extension Gamma *_C (C x Z) lies in the permutational class whenever C is the intersection of Gamma with the stabilizer of two points of one orbit of a type (A) action of an overgroup, via the edge-shrinking embedding u -> w x w x^-1
distinct_from:
  free-permutational-products-preserve-pbh: that reduces identity-edge extensions to lamplighter wreaths over the coset space Gamma/C; this avoids the coset space of C altogether, by shrinking a point-stabilizer edge to a pair-stabilizer edge.
  bh-type-a-class-closed-under-permutational-lamp-wreaths: that gives the lamp wreath over a type (A) set, hence identity-edge extensions over point stabilizers; this extends the conclusion to intersections of two conjugate point stabilizers, which are usually not point stabilizers of any type (A) action.
  pbh-closed-under-decidable-permutational-wreaths: that is the open wreath closure over arbitrary decidable stabilizers; this settles the identity-edge consequence of it for every pair-stabilizer edge.
  baumslag-gersten-pbh-reduces-to-higman-group-and-a-lamp-wreath: that needs a lamp wreath over Gamma/<a_0>; this replaces that input by a pair-stabilizer condition on an actor for H_4 ⋊ C_4.
---

**ESTABLISHED** (lane proof, elementary Britton argument on top of landed closures; not yet
refereed; no priority claimed).

## Statement

1. **Edge shrinking.** Let `Γ` be a group, `P ≤ Γ`, `x ∈ Γ`, and `C = P ∩ xPx^-1`. In
   `L = Γ *_P (P × ⟨w⟩)`, put `v = w x w x^-1`. Then `ρ : Γ *_C (C × ⟨u⟩) → L`, identity on `Γ` and
   `u ↦ v`, is injective.
2. **Closure.** Let `Γ_A` act on `X` with type (A), `Γ ≤ Γ_A`, `p ∈ X`, `x ∈ Γ_A`, and
   `C = Γ ∩ Stab(p) ∩ Stab(xp)`. Then `Γ *_C (C × Z) ∈ B_A`, so it embeds in a finitely presented
   simple group. With `x = 1`, this is the point-stabilizer case.
3. **Iteration.** Applying item 1 again to `P' = P ∩ xPx^-1` shrinks the edge to the stabilizer of
   the four points `p, xp, yp, yxp`, and so on for cubes `{x_S p}`.

## Consequence for `BG`

By `baumslag-gersten-pbh-reduces-to-higman-group-and-a-lamp-wreath`, item 1,
`BG ≤ Γ *_(⟨a_0⟩)(⟨a_0⟩ × Z)` for every `Γ ⊇ H_4 ⋊ C_4`. So `BG ∈ B_A` as soon as some type (A)
actor `Γ_A ⊇ H_4 ⋊ C_4` has points `p` and `q = xp` with
`(H_4 ⋊ C_4) ∩ Stab(p) ∩ Stab(q) = ⟨a_0⟩`. This needs no wreath conjecture. The regular-orbit
invariant (`type-a-actors-have-no-proper-power-cyclic-edge-splittings`) forbids `⟨a_0⟩` only as an
orbit-finite point stabilizer, not as a pair stabilizer inside a larger actor.

## Lesson for general BH

Identity-edge permanence, and with it the untwisted half of HNN permanence, reduces to one
question: can the edge be seen as a two-point stabilizer in some type (A) actor?

Coset spaces `Γ/C` of bad edges, such as proper-power cyclic ones, are never type (A) spaces. But
the edge-shrinking product `w · x w x^-1` lets a good big edge `P` carve out `P ∩ xPx^-1`. So
"intersection of two conjugate point stabilizers" is the right notion of a good edge. Designing
hosts should therefore aim at controlling pair stabilizers, not coset actions.

## Proof

**Item 1.**
- *Well defined.* `w` centralizes `P ⊇ C`, and `x w x^-1` centralizes `xPx^-1 ⊇ C`, so `v`
  centralizes `C`.
- *The degenerate case.* If `x ∈ P`, then `C = P`, `v = w^2` and `ρ` is clearly injective. So assume
  `x ∉ P`.
- *Setup.* Write `v = w_L x w_R x^-1` and `v^-1 = x w_R^-1 x^-1 w_L^-1`. Take a reduced word
  `g_0 u^(e_1) g_1 ⋯ u^(e_k) g_k` with `k ≥ 1` and `g_i ∉ C` whenever `e_i = −e_(i+1)`, and substitute.
  In `L` a pinch is a subword `w^ε g w^-ε` with `g ∈ P`.
  - *Inside one `v^(±1)`* the two `w`-letters have the same sign, so there is no pinch.
  - *At a junction with `e_i = e_(i+1)`* the adjacent letters have the same sign, so there is no
    pinch.
- *Junction `v g v^-1`* (with `g = g_i ∉ C`). The inner subword `w_R x^-1 g x w_R^-1` pinches iff
  `x^-1 g x ∈ P`, that is `g ∈ xPx^-1`. After it, the next subword is `w_L g w_L^-1`, which pinches
  iff `g ∈ P`. Both would give `g ∈ C`, so at most one pinch happens.
- *Junction `v^-1 g v`.* Symmetric: first `w_L^-1 g w_L` (needs `g ∈ P`), then
  `w_R^-1 (x^-1 g x) w_R` (needs `g ∈ xPx^-1`). At most one of these holds.
- *No cascades.* If both letters of some `v^(e_i)` are consumed, by its left and its right junction,
  then `e_(i−1) = e_(i+1) = −e_i`. The newly adjacent letters come from `v^(e_(i−1))` and
  `v^(e_(i+1))`, so they have the same sign and cannot pinch.
- *Conclusion.* So the reduction stops after at most one pinch per junction. Of the `2k` letters, at
  least `2k − 2(k−1) = 2` remain, and what is left is reduced. By Britton's lemma `ρ(g) ≠ 1`.

**Item 2.**
- Put `P = Stab_(Γ_A)(p)` and `C' = P ∩ xPx^-1 = Stab(p) ∩ Stab(xp)`. Since `Γ ∩ C' = C`,
  Britton's lemma gives `⟨Γ, u⟩ = Γ *_C (C × ⟨u⟩)` inside `Γ_A *_(C') (C' × ⟨u⟩)`.
- By item 1 the latter embeds in `Γ_A *_P (P × Z)`.
- The standard isomorphism identifies `Γ_A *_P (P × Z)` with the free permutational product
  `Z *_(Γ_A/P) Γ_A`, and `Γ_A/P ≅ Γ_A·p`.
- `Z/2 wr_(Γ_A·p) Γ_A` is a subgroup of `Z/2 wr_X Γ_A`, which lies in `B_A` by
  `bh-type-a-class-closed-under-permutational-lamp-wreaths`.
- Part 1 of `free-permutational-products-preserve-pbh` (lane proof, not reviewed) then puts
  `Z *_(Γ_A·p) Γ_A` in `B_A`, and `B_A` is closed under subgroups.

**Item 3.** Item 1 needs no hypothesis on `P`, so it applies to `P'` and composes. `∎`
