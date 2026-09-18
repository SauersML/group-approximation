---
rg: 2
id: baumslag-gersten-in-b-a-from-a-root-separated-shift
kind: claim
title: The Baumslag--Gersten group lies in B_A as soon as some B_A group contains a shift configuration (a, τ), with (τaτ^-1) a (τaτ^-1)^-1 = a^2 and a of infinite order, together with a realized subgroup that contains a but none of its proper roots in the base of <a, τaτ^-1>; no Higman group is needed
requires:
  - baumslag-gersten-pbh-reduces-to-higman-group-and-a-lamp-wreath
  - pbh-coset-wreaths-iff-identity-edge-hnns
  - bs12-base-generator-centralizer-proof
distinct_from:
  baumslag-gersten-pbh-reduces-to-higman-group-and-a-lamp-wreath: that asks for a B_A overgroup of H_4 ⋊ C_4 in which <a_0> itself is realized; this asks only for some shift configuration in some B_A group, and for a realized subgroup that separates a from its roots, observing that the Britton argument there uses nothing about H_4.
  higman-chain-group-lies-in-b-a: that settles the base K of the HNN splitting of BG; this isolates what the HNN step needs, a single conjugator.
  baumslag-solitar-chains-of-every-length-lie-in-b-a: that places every finite piece of the bi-infinite chain T_Z inside BG; this says the only missing ingredient is the shift.
---

**ESTABLISHED** (lane proof, elementary; not reviewed; no priority claimed).

`BG = ⟨a, t | (t a t^-1) a (t a t^-1)^-1 = a^2⟩`. A **shift configuration** in a group `Γ` is a pair
`(a_0, τ)` such that `a_1 = τ a_0 τ^-1` satisfies `a_1 a_0 a_1^-1 = a_0^2`, with `a_0` of infinite
order. Then `A = ⟨a_0, a_1⟩ ≅ BS(1,2)` (Step 0 of `bs12-base-generator-centralizer-proof`). Let
`N = ⋃_j a_1^-j ⟨a_0⟩ a_1^j ≅ Z[1/2]` be its base, which consists of the dyadic roots `a_0^q` of `a_0`.

## Statement

1. **Criterion.** Let `Γ ∈ B_A` contain a shift configuration `(a_0, τ)`, and suppose some `D ≤ Γ` is
   realized (condition (e) of `pbh-coset-wreaths-iff-identity-edge-hnns`), with `a_0 ∈ D` and
   `D ∩ N = ⟨a_0⟩`. Then `BG ∈ B_A`, and `BG` embeds in a finitely presented simple group.
2. **Special case.** If `⟨a_0⟩` itself is realized in `Γ`, take `D = ⟨a_0⟩`. With `Γ ⊇ H_4 ⋊ C_4` this
   is the known reduction, and the Higman quotient plays no other role.
3. **Where shift configurations cannot live.** None exists in a soluble group, a linear group, a finite
   product of linear groups, or a group of tame homeomorphisms.

## Proof

- **Item 1, the separator.** Put `D' = D ∩ C_Γ(a_0)`. It is realized: centralizers are realized in any
  `B_A` group, and realized subgroups are closed under finite intersections. Then:
  - `A ∩ D' = C_A(a_0) ∩ D = N ∩ D = ⟨a_0⟩`, because the centralizer of a nontrivial base element of
    `BS(1,2)` is the base;
  - `A ∩ τ D' τ^-1 = C_A(a_1) ∩ τ D τ^-1 = ⟨a_1⟩`, because the centralizer of the stable letter is
    `⟨a_1⟩`, and `a_1 = τ a_0 τ^-1 ∈ τ D τ^-1`.
- **Item 1, the embedding.** Let `L = Γ *_(D') (D' × ⟨u⟩)`. It lies in `B_A` by (e) ⟹ (d). Define
  `ρ : BG -> L` by `a ↦ a_0` and `t ↦ τ u`. It is well defined, since `u` centralizes `a_0`.
  - Write `BG = A*_φ` with `φ : ⟨a_0⟩ -> ⟨a_1⟩`. Take a reduced word `x_0 t^(ε_1) x_1 ⋯ t^(ε_k) x_k`
    with `x_i ∈ A`.
  - In the image, the `Γ`-syllable between `u` and `u^-1` is `x_i`, and between `u^-1` and `u` it is
    `τ^-1 x_i τ`. These are pinches exactly when `x_i ∈ A ∩ D' = ⟨a_0⟩`, respectively when
    `x_i ∈ A ∩ τ D' τ^-1 = ⟨a_1⟩`. That is exactly when the word has a pinch in `BG`.
  - So by Britton's lemma `ρ` is injective. This is the argument of
    `baumslag-gersten-pbh-reduces-to-higman-group-and-a-lamp-wreath` with `C_1` replaced by `D'`. It uses
    no property of `Γ` beyond the configuration.
  - Finally, `BG` is finitely generated (`type-a-action-gives-boone-higman-for-subgroups`).
- **Item 3.**
  - *Soluble.* `BG' = ⟨⟨a⟩⟩` is perfect: each `a_i = t^i a t^-i` is a commutator of `a_i` with
    `a_(i+1)`. So in a soluble image `a` dies.
  - *Linear.* From `a_1 ~ a_0` and `a_1 a_0 a_1^-1 = a_0^2`, some power of each element is unipotent.
    The argument for the chain in `higman-chain-configuration-reduction-proof` then gives that `a_0` has
    finite order.
  - *Tame.* `tame-power-conjugators-have-more-hyperbolic-points` gives `F_(a_0) ⊊ F_(a_1)`. But `a_1` is
    conjugate to `a_0`, so these sets have the same size. ∎

## How a host could arise

`BG = T_Z ⋊ ⟨t⟩`, where `T_Z = ⟨⟨a⟩⟩` is the bi-infinite chain with `a_(i+1) a_i a_(i+1)^-1 = a_i^2`.
- Any action of `T_Z` on a space `Y` induces an action of `BG` on `Z × Y`. On the copy `{k} × Y`, the
  element `a` acts as `a_(-k)` does on `Y`.
- So a shift configuration in homeomorphisms amounts to a tower of homeomorphisms `s_k`, `k ∈ Z`, of
  one space, with `s_(k+1) s_k s_(k+1)^-1 = s_k^2`. On the line: `s_0 = x + 1`, `s_1 = 2x`, and `s_2` is a
  square map. For negative `k`, `s_(-1)` must be conjugated by a translation to its own square. On
  `[n, n+1]` it must look like a flow at time `2^n`.
- Such towers are of **exponential type**, with infinitely many hyperbolic fixed points. A `B_A` host
  must code them finitely. None is claimed here.

## Lesson for general BH

**For HNN inputs the whole problem is one conjugator.** The vertex group, the edge embeddings, and
faithfulness are all free: Britton plus a realized separator. What remains is a single element `τ` that
conjugates the edge generator to its image **inside a `B_A` group**. For `BG` that element forces
self-similarity of the chain (a shift symmetry). The obstructions show it must be non-soluble,
non-linear and non-tame. So finite constructions such as wreath towers or chain amalgams, which build
every finite piece, can never supply it. It has to come from a host with a genuine **renormalization**:
an element conjugating "translation" to "dilation" across infinitely many scales at once.
