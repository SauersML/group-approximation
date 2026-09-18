---
rg: 2
id: baumslag-gersten-pbh-reduces-to-higman-group-and-a-lamp-wreath
kind: claim
title: If Higman's group H_4 lies in the permutational class inside an actor Gamma, and the lamplighter Z/2 wr over the cosets of <a_0> in Gamma does too, then the Baumslag--Gersten group lies in the permutational class
distinct_from:
  baumslag-gersten-group-maps-onto-higman-groups: that proves BG maps onto H_n ⋊ C_n; this uses that quotient as a conjugating overgroup, which untwists BG into an identity-edge HNN extension.
  baumslag-gersten-splits-over-bs12-edges: that reduces BG to a symmetric actor for the height-two tower plus faithfulness; this reduces BG to H_4 plus one lamplighter wreath, and needs no faithfulness argument.
  bh-embeddability-survives-decidable-edge-hnn: that is the general HNN permanence; its bh-free-10 attempt records the untwisting for conjugation-induced edges, and this is its instance for BG, where the conjugating overgroup is forced to contain a Higman-type quotient.
  higman-group-satisfies-boone-higman: that is the open Higman test case; this makes it, plus a wreath closure, sufficient for the Baumslag--Gersten test case.
---

**ESTABLISHED** (conditional implication; lane proof, elementary; no priority claimed). Reviewed:
gq-referee-a PASS (`research/artifacts/gq-referee-a-baumslag-gersten-pbh-reduces-to-higman-group-and-a-lamp-wreath.md`,
834cfa8c3; nits N1–N3 applied).

## Statement

Let `H_4 ⋊ C_4 = BG/⟨⟨t^4⟩⟩` be as in `baumslag-gersten-group-maps-onto-higman-groups`, with
generators `a_0, …, a_3` of `H_4` and `τ a_i τ^-1 = a_(i+1)`. Suppose `H_4 ⋊ C_4 ≤ Γ` with
`Γ ∈ B_A`. Then:
1. `BG` embeds in the identity-edge extension `Γ *_(⟨a_0⟩) (⟨a_0⟩ × Z)`, via `a ↦ a_0` and
   `t ↦ τ u`;
2. hence `BG ∈ B_A` if `Z/2 wr_(Γ/⟨a_0⟩) Γ ∈ B_A`. The standard isomorphism
   `Γ *_C (C × Z) ≅ Z *_(Γ/C) Γ` (free permutational product), valid for infinite `C`, turns this
   into part 1 of `free-permutational-products-preserve-pbh` (bh-free-10, lane proof, not reviewed).
   Part 3 there covers finite `C` only.

Since `B_A` is closed under finite-index overgroups, the hypothesis on `Γ` holds as soon as
`H_4 ∈ B_A`. The wreath is an instance of the open `pbh-closed-under-decidable-permutational-wreaths`.
It needs decidable membership in `⟨a_0⟩ ≤ Γ`. For `Γ = H_4 ⋊ C_4` this is the power problem for
`a_0` in Higman's group. It was not checked here, and no source is recorded. Normal forms for the
square of groups (Martin, arXiv:1506.02837) are the natural place to look.

**Necessity of a Higman-type quotient.** Any conjugating overgroup `Γ ⊇ BS(1,2) = ⟨a, b⟩` with
`γ a γ^-1 = b` contains the quotient `⟨a, γ⟩` of `BG`, in which `BS(1,2)` survives. In that quotient
`a_2 = γ b γ^-1 ∉ ⟨a, b⟩`, because inside `BS(1,2)` the exponent homomorphism `a_0 ↦ 0`, `a_1 ↦ 1` would send the relation
`a_2 a_1 a_2^-1 = a_1^2` to `1 = 2`.
So such a `Γ` needs at least a quotient of the tower `K` with `BS(1,2)` intact. `H_n ⋊ C_n` is the
standard such quotient.

## What the wreath input cannot come from

The established lamp-wreath closure (`bh-type-a-class-closed-under-permutational-lamp-wreaths`)
needs `Γ ↷ Γ/⟨a_0⟩` to be of type (A). That forces finitely many orbits of the point stabilizer
`⟨a_0⟩` on `Γ/⟨a_0⟩`. Since `a_0 ~ a_0^2` in `Γ`, the regular-orbit invariant of
`type-a-actors-have-no-proper-power-cyclic-edge-splittings` then makes `Γ/⟨a_0⟩` finite, which is
absurd. The finite-stabilizer closure (`permutational-boone-higman-closed-under-wreath-products`)
does not apply either.

So item 2 needs the open decidable case, `pbh-closed-under-decidable-permutational-wreaths`, over a
proper-power cyclic stabilizer. Coset spaces of proper-power cyclic subgroups are never type (A)
spaces. Any proof of that case must put the wreath in an actor that does not act on `Γ/⟨a_0⟩`.

**Edge shrinking does not work (2026-09-18).** A natural way around the coset space is to shrink a
point-stabilizer edge `P` of a type (A) action to `C = P ∩ xPx^-1`, via
`Γ *_C (C × ⟨u⟩) → Γ *_P (P × ⟨w⟩)` with `u ↦ v = w x w x^-1`. This map is well defined but not
injective in general.
- For `g_1 ∈ xPx^-1` one has `v g_1 v^-1 = w g_1 w^-1`.
- So for `g_2 ∈ (P ∩ g_1^-1 P g_1) ∖ C`, the reduced word `u g_1 u^-1 g_2 u g_1^-1 u^-1` maps to
  `g_1 g_2 g_1^-1 ∈ Γ`.

The same collapse happens for every `v` that agrees with a conjugate of `w` on `xPx^-1`. Pair
stabilizers are therefore not automatically good edges.

## Lesson for general BH

HNN permanence splits into two independent inputs.
- A *conjugating overgroup* realizes the edge map by an honest conjugation. This input is a
  quotient-permanence problem: only a quotient of the HNN extension, faithful on the vertex group,
  has to land in `B_A`.
- *Identity-edge permanence* is a lamplighter-wreath closure.

For `BG` the first input is exactly Higman's group. So the two flagship torsion-free test cases
are not independent: `H_4` plus a wreath closure settles `BG`. Work on one feeds the other, and the
remaining novelty sits in the wreath closure over the cyclic edge `⟨a_0⟩`.

**General form.** The proof uses nothing about `BG` except `τ C_1 τ^-1 = φ(C_1) = C_2`. So for any
HNN extension `G = A*_φ` and any `n`, the cyclic quotient `G/⟨⟨t^n⟩⟩` is a conjugating overgroup
as soon as `A` survives in it. That quotient is `P_n ⋊ C_n`, where `P_n` is the polygon of `n`
copies of `A` glued cyclically along `φ`. Then `G ≤ Γ *_(C_1)(C_1 × Z)` for every `Γ ∈ B_A`
containing it.

For Magnus steps of one-relator groups, `A` should survive in `P_n` for large `n` by Gersten--Stallings
curvature, since Magnus intersections are small. That was not checked here. So one-relator
permanence reduces to polygon-of-groups permanence plus identity-edge permanence.

## Proof

Put `A = ⟨a_0, a_1⟩ ≅ BS(1,2)` (Higman; cited in `baumslag-gersten-group-maps-onto-higman-groups`),
`C_1 = ⟨a_0⟩`, `C_2 = ⟨a_1⟩ = τ C_1 τ^-1 ⊆ A`, so `φ = c_τ|_(C_1)` and `BG = A*_φ`. Let
`L = Γ *_(C_1)(C_1 × ⟨u⟩)`, the HNN extension of `Γ` in which `u` centralizes `C_1`. Define
`ρ : BG → L` by `ρ|_A = id` and `ρ(t) = τ u`. It is well defined because
`τ u c u^-1 τ^-1 = τ c τ^-1 = φ(c)` for `c ∈ C_1`.

**Injectivity (Britton).** Take a reduced word `g = x_0 t^(ε_1) x_1 ⋯ t^(ε_k) x_k` of `BG`, with
`x_i ∈ A` and `k ≥ 1`. Its image is a word in `Γ` and `u^(±1)`. Between consecutive letters `u`, the
`Γ`-syllables are as follows.
- `ε_i = 1, ε_(i+1) = −1`: the syllable `u x_i u^-1` is a pinch iff `x_i ∈ C_1`, exactly as for
  `t x_i t^-1` in `BG`.
- `ε_i = −1, ε_(i+1) = 1`: the syllable `u^-1 (τ^-1 x_i τ) u` is a pinch iff
  `τ^-1 x_i τ ∈ C_1`, iff `x_i ∈ τ C_1 τ^-1 = C_2`, exactly as for `t^-1 x_i t`.
- Equal signs give no pinch, in either group.

So reduced words go to reduced words, and by Britton's lemma `ρ(g) ≠ 1`. For `k = 0`, `ρ` is the
inclusion `A ≤ Γ`.

**Item 2.** Apply the isomorphism of item 2 with `C := ⟨a_0⟩`, then part 1 of the cited node
with `W := Γ`, `K := Z` and `X := Γ/⟨a_0⟩`. `∎`
