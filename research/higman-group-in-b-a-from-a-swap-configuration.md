---
rg: 2
id: higman-group-in-b-a-from-a-swap-configuration
kind: claim
title: H4 ⋊ C_2 is the amalgam of the chain group G_1 with F(a,c) ⋊ C_2 along F(a,c), the involution swapping the top letter a with the bottom base c; so H4 ∈ B_A as soon as a B_A overgroup of G_1 contains such a swap involution and a realized subgroup cutting G_1 and F(a,c) ⋊ C_2 exactly in F(a,c)
distinct_from:
  higman-group-satisfies-boone-higman: that is the open question; this reduces it to a single involution in a B_A overgroup of the chain group G_1, plus a separator.
  baumslag-gersten-in-b-a-from-a-root-separated-shift: that reduces BG to a shift of infinite order; this reduces H4 to a swap of order two, which is the periodic version of the same renormalization.
  higman-group-splits-as-amalgams-over-free-subgroups: that gives H4 = G_1 *_(F_2) G_1; this folds the two vertex groups into one by the rotation by two, so only one copy of G_1 has to be placed.
---

**ESTABLISHED** (lane proof, elementary; not reviewed; no priority claimed). It does not use
`higman-chain-group-lies-in-b-a`, which a referee failed (OPEN again); the criterion assumes a host containing `G_1`.

`H4 = ⟨g_0, …, g_3 | g_(i+1) g_i g_(i+1)^-1 = g_i^2, i ∈ Z/4⟩`. The rotation `ρ(g_i) = g_(i+2)` is an
automorphism of order two. Write `G_1 = ⟨g_0, g_1, g_2⟩ = ⟨a, b, c | a^-1 b a = b^2, b^-1 c b = c^2⟩`
with `a = g_2^-1`, `b = g_1^-1` and `c = g_0`. Put `F = ⟨a, c⟩`, which is free of rank two
(`higman-group-splits-as-amalgams-over-free-subgroups`).

## Statement

1. **Folding.** `H4 ⋊_ρ C_2 ≅ G_1 *_F (F ⋊ ⟨σ⟩)`, where `σ^2 = 1`, `σ a σ = c^-1` and `σ c σ = a^-1`.
2. **Criterion.** Suppose there are `L ∈ B_A` with `G_1 ≤ L`, an involution `σ ∈ L` with
   `σ a σ = c^-1`, and `D ≤ L` realized in `L`, such that
   `G_1 ∩ D = F = ⟨F, σ⟩ ∩ D` and `⟨F, σ⟩ ≅ F ⋊ C_2`. Then `H4 ∈ B_A`. So `H4` embeds in a finitely
   presented simple group.
3. **Where swap configurations cannot live.** An involution conjugating `a` to `c^-1` does not exist in
   any `B_A` overgroup `L` of `G_1` that is soluble or linear, or in which `a`, `b` and `c` act as tame
   homeomorphisms.

## Proof

- **Item 1.**
  - `ρ` maps `⟨g_0, g_1, g_2⟩` onto `⟨g_2, g_3, g_0⟩` and swaps `g_0` and `g_2`, so it preserves `F`.
  - In `P = G_1 *_F (F ⋊ ⟨σ⟩)`, Bass–Serre theory gives `⟨G_1, σ G_1 σ⟩ = G_1 *_F σ G_1 σ`. This is the
    index-two kernel of `P -> C_2`. The second copy is glued to the first by `σ x σ` for `x ∈ F`, that
    is, by the swap `a ↔ c^-1`, `c ↔ a^-1`.
  - With `g_3 := σ g_1 σ` this is the presentation of the splitting
    `H4 = ⟨g_0, g_1, g_2⟩ *_(⟨g_0, g_2⟩) ⟨g_2, g_3, g_0⟩`, with `σ` acting as `ρ`.
- **Item 2.** Apply item 1 of `pbh-amalgams-over-centralizer-separated-edges` to `X = G_1`,
  `Y = ⟨F, σ⟩` and `C = F` in `L`. This gives `P ∈ B_A`, and `H4 ≤ P`.
- **Item 3.**
  - *Soluble.* `H4` is perfect, since `g_i = [g_(i+1), g_i]`. The group `⟨G_1, σ⟩ ≤ L` is an image of
    `H4 ⋊ C_2` (by item 1, via the universal property of the amalgam) with `G_1` faithful. In a soluble
    `L`, `H4`, and with it `G_1`, would map trivially.
  - *Linear.* `H4` has no nontrivial finite quotient, so its image in a finitely generated linear group is
    trivial (Malcev).
  - *Tame.* By `tame-power-conjugators-have-more-hyperbolic-points` applied to `b` and `a`, and to `c`
    and `b`, `F_c ⊊ F_b ⊊ F_a`. But `σ` conjugates `a` to `c^-1`, so `|F_a| = |F_c|`. ∎

## The two open inputs, side by side

| input | vertex group | conjugator needed | order |
|---|---|---|---|
| `BG` | `BS(1,2)` (in `B_A`); `K ≅ G_1` OPEN | shift `τ`: `a_0 ↦ a_1` | infinite |
| `H4 ⋊ C_2` | `G_1` (OPEN) | swap `σ`: `a ↔ c^-1` | two |

In both cases the conjugator must identify the **top** of a Baumslag–Solitar chain (a letter that
survives in the abelianization) with the **bottom** (an element conjugate to its own square). So it must
destroy the abelianization grading that the wreath and amalgam constructions all respect. The
separators are a second, lesser problem.

## Lesson for general BH

**Beyond the chain group, the obstruction for the Higman and Baumslag–Gersten test cases is a grading,
not a configuration.** The pieces (`G_1`, finite chains) are local problems, OPEN again after the
referee. Even once they are solved, the constructions that place pieces (wreath towers, centralizer
amalgams) preserve a Z-grading in which the top of the tower has degree one and the bottom has degree
zero. The input needs an element that exchanges them. This
requires a host that is perfect along the tower, non-linear and non-tame: a renormalization, periodic
(`H4`) or aperiodic (`BG`). A useful general test for any proposed universal construction: can it make
the top and bottom of a BS chain conjugate? If it preserves a height function, it cannot reach
`H4` or `BG`.
