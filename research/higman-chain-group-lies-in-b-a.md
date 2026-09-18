---
rg: 2
id: higman-chain-group-lies-in-b-a
kind: claim
title: The chain BS(1,2) *_Z BS(1,2), the common vertex group of Higman's group and the base of the Baumslag--Gersten group, lies in B_A and embeds in a finitely presented simple group, because a Kaloujnine--Krasner twist puts its chain configuration in the coset lamplighter BS(1,2) wr over BS(1,2)/<b>
requires:
  - higman-chain-group-pbh-iff-chain-configuration
  - bs12-base-generator-is-a-centralizer-in-b-a
  - pbh-amalgams-over-centralizer-separated-edges
  - char-zero-linear-groups-satisfy-permutational-boone-higman
  - type-a-action-gives-boone-higman-for-subgroups
distinct_from:
  higman-chain-group-pbh-iff-chain-configuration: that reduces the question to finding a chain configuration in some B_A group, and names the twisted lamplighter M_1 as the canonical candidate without placing it; this places M_1, and so decides the question.
  bs12-base-generator-is-a-centralizer-in-b-a: that puts the untwisted coset lamplighters Λ wr_(A/<b>) A in B_A; this observes that the twisted one embeds in the untwisted one with the larger lamp group BS(1,2).
  higman-group-satisfies-boone-higman: that is the open question for Higman's group; this settles its vertex group, and leaves the cyclic closing-up of four chains as the whole remaining difficulty.
  baumslag-gersten-group-satisfies-boone-higman: that is the open question for BG; this settles its base K, and leaves the shift HNN step.
---

**ESTABLISHED** (lane proof, elementary; not reviewed; no priority claimed).

It inherits the status of the unreviewed lane chain `bs12-base-generator-is-a-centralizer-in-b-a`, which
rests on `lamp-wreaths-over-psl2-tree-vertices-lie-in-b-a` and `pbh-coset-wreaths-iff-identity-edge-hnns`.
It also inherits the status of `pbh-amalgams-over-centralizer-separated-edges`, item 3. The embedding
lemma below is classical.

## Statement

Let `G_1 = ⟨a, b, c | a^-1 b a = b^2, b^-1 c b = c^2⟩`. Put `A = ⟨a, b⟩ ≅ BS(1,2)`, `C = ⟨b⟩`, and
`E = ⟨b, c⟩ = Z[1/2] ⋊ ⟨b⟩ ≅ BS(1,2)`.

1. **Twisted lamps embed in untwisted ones.** Let `C ≤ A` be groups, and let `E = N ⋊ C`. Then
   the twisted coset lamplighter `(⊕_(A/C) N) ⋊ A` embeds in the coset lamplighter `E wr_(A/C) A`. In the
   twisted lamplighter, `A` permutes the summands and `C` acts on the summand at `C` as it acts on `N`.
2. **M_1 ∈ B_A.** `M_1 = G_1/[N_c, N_c]`, where `N_c` is the normal closure of `c`, lies in `B_A`.
3. **G_1 ∈ B_A.** So `G_1` embeds in a finitely presented simple group. So does `K ≅ G_1`, the height-two
   tower inside the Baumslag–Gersten group.
4. **General form.** Let `A ∈ B_A`, and let `C ≤ A` satisfy condition (e) of
   `pbh-coset-wreaths-iff-identity-edge-hnns`. Let `Y = N ⋊ C ∈ B_A` with `C = C_Y(S)` for a finite set
   `S` commuting with `C`. Then `A *_C Y ∈ B_A`.

## Proof

- **Item 1 (Kaloujnine–Krasner with a twist).** Fix a transversal `T ∋ 1` of `A/C`. For `a ∈ A` and
  `t ∈ T`, write `a t = t' κ(a, t)` with `t' ∈ T` and `κ(a, t) ∈ C`. Define `κ_a : A/C -> C` by
  `κ_a(t'C) = κ(a, t)`.
  - *The top group.* `ψ(a) = (κ_a, a) ∈ C^(A/C) ⋊ A ≤ E wr_(A/C) A` is a homomorphism. The cocycle
    identity `κ_(aa')(y) = κ_a(y) κ_(a')(a^-1 y)` is the standard computation: if `a' t = t' c'` and
    `a t' = t'' c`, then `a a' t = t'' c c'`.
  - *The lamps.* Send `n` in the summand at `tC` to the function with value `n ∈ N ≤ E` at `tC` and `1`
    elsewhere.
  - *Equivariance.* `ψ(a)` moves the lamp at `tC` to `t'C`, where `a t = t' c`, and conjugates its value
    by `κ_a(t'C) = c`. That is the twisted action.
  - *Injectivity.* The composite to the top group `A` is the identity on `A`, and the lamp map is
    injective.
- **Item 2.** By the Bass–Serre computation in `higman-chain-configuration-reduction-proof`,
  `N_c = *_(A/C) g N_0 g^-1` with `N_0 = Z[1/2]`. So `M_1` is the twisted coset lamplighter of item 1 with
  `N = Z[1/2]`, where `b` acts on the summand at `C` as `b^-1 c b = c^2` does. Here `N ⋊ C = E ≅ BS(1,2)`.
  So `M_1 ≤ BS(1,2) wr_(A/⟨b⟩) A`.
  - `BS(1,2) ≤ GL_2(Q)` lies in `B_A` by `char-zero-linear-groups-satisfy-permutational-boone-higman`.
  - Item 2 of `bs12-base-generator-is-a-centralizer-in-b-a`, with `Λ = BS(1,2)`, puts
    `BS(1,2) wr_(A/⟨b⟩) A` in `B_A`.
  - `B_A` is closed under subgroups.
- **Item 3.** `M_1` contains the chain configuration `(a, b, c)`: `c` maps to a generator of `Z[1/2]` in
  the summand at `C`, which has infinite order. By (2) ⟹ (1) of
  `higman-chain-group-pbh-iff-chain-configuration`, `G_1 ∈ B_A`. `G_1` is finitely generated, so
  `type-a-action-gives-boone-higman-for-subgroups` embeds it in a finitely presented simple group. The
  isomorphism `G_1 ≅ K` is in the reduction proof.
- **Item 4.** Put `L = Y wr_(A/C) A`, which lies in `B_A` by (e) ⟹ (b). Let `X = ψ(A)` and
  `Y' = ⟨N_C, ψ(C)⟩`, where `N_C` is the lamp group at the coset `C`.
  - `ψ(c)` conjugates the lamp at `C` by `c`. So `Y' ≅ N ⋊ C = Y`.
  - `X ∩ Y' = ψ(C)`. If `n·ψ(c) = ψ(a)` with `n ∈ N_C`, the top parts give `a = c`, and then `n = 1`.
  - The retraction `Y -> C`, the set `S`, and the realization of `C` in `A` are the three hypotheses of
    item 3 of `pbh-amalgams-over-centralizer-separated-edges`.

  So `A *_C Y ∈ B_A`. For `G_1` take `Y = E` and `S = {b}`. In `Z[1/2] ⋊ ⟨b⟩` an element commuting with
  `b` has zero base part, so `C_E(b) = ⟨b⟩`. ∎

## Consistency with the recorded obstructions

- `M_1` and `L` are soluble of derived length at most 4, and of infinite Hirsch length, as
  `finite-hirsch-length-soluble-groups-hold-no-bs-chain` demands.
- `L` is neither linear nor metabelian, since it contains a configuration. No tame-homeomorphism
  structure is claimed, so `tame-power-conjugators-have-more-hyperbolic-points` does not apply.
- Item 4 of `pbh-amalgams-over-centralizer-separated-edges` says amalgams and HNN steps never create a
  configuration. The configuration here comes from a **wreath** step, which that item does not cover.

## What is left for H4 and BG

- **Higman's group.** `H4 = G_1 *_(F_2) G_1'`, with edge `⟨g_0, g_2⟩`. Item 1 of the amalgam engine needs
  a `B_A` group containing both vertex groups, glued along the edge, and a realized separating subgroup.
  So what remains is to close **four** chains into a cycle `(g_0, g_1, g_2, g_3)`, with each consecutive
  triple generating a faithful `G_1`. Wreath towers produce chains of any finite length. A cycle needs an
  element acting as the top of a tower that it itself sits at the bottom of.
- **Baumslag–Gersten.** `BG = K*_ψ`, with `ψ` shifting the tower `(a_0, a_1) -> (a_1, a_2)`. Item 2 of the
  engine needs a `B_A` group containing `K` together with a conjugator that realizes the shift, that is,
  a bi-infinite chain with a shift symmetry.

## Lesson for general BH

**Wreathing creates what amalgams cannot.** The graph-of-groups engine reduces an amalgam to a local
configuration, and it can never create one. A coset-lamplighter wreath, read through the
Kaloujnine–Krasner cocycle, turns the stabilizer's action on a lamp into a twist. That manufactures the
missing configuration from untwisted pieces: `C` acts on `N`, and `N ⋊ C` becomes the lamp group. So
**twisted = untwisted with a bigger lamp**, and centralizer realization of `C` (condition (e)) is the only
input. Together with the amalgam engine this gives a constructor:
`A *_C (N ⋊ C) ∈ B_A` whenever `C` is realized in `A` and self-centralizing up to a finite set in
`N ⋊ C`. This turns BH for towers and chains of HNN/amalgam type into the single question of **propagating
centralizer realization up the tower** (is `⟨c⟩` realized in `G_1`?). Cycles and shifts, as in `H4` and
`BG`, are the genuinely global part.
