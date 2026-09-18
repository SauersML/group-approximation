---
rg: 2
id: pbh-closed-under-permutational-wreaths-with-infinite-stabilizers
kind: claim
refuted_by:
  - pbh-wreath-closure-fails-over-undecidable-stabilizers
title: The permutational Boone--Higman class is closed under restricted permutational wreath products over arbitrary countable G-sets
distinct_from:
  permutational-boone-higman-closed-under-wreath-products: that is the established case of G-sets with finite point stabilizers, through free orbits of the relative automorphism actor; this asks for arbitrary countable G-sets, where lamps sit over infinite stabilizers.
artifacts:
  - research/artifacts/solve-bh-free-solvable-2026-09-13.md
---

**REFUTED as stated** (2026-09-18) by `pbh-wreath-closure-fails-over-undecidable-stabilizers`.
For all groups `A` and `G` in `B_A` and every countable `G`-set `X`, the
restricted permutational wreath product `A wr_X G = A^(X) ⋊ G` lies in `B_A`.

**Why it fails.** The word problem of `A wr_(G/C) G` decides membership in `C`, since
`δ_(gC) δ_C = 1` iff `g ∈ C`. Mihailova's subgroup `C <= F_2 × F_2` has undecidable
membership, so `Z/2 wr_(G/C) G` with `G = F_2 × F_2` is a finitely generated group with
unsolvable word problem, and is not in `B_A`. The corrected statement, with point
stabilizers of decidable membership, is `pbh-closed-under-decidable-permutational-wreaths`
(OPEN). Its test cases include both test cases listed below.

**Source.** This is the remaining part of the wreath-product clause of Zaremsky's
Question 5.7 (arXiv:2405.18354, TeX l.534--536, quoted in
`permutational-boone-higman-closed-under-wreath-products`), in the embedding form of
the permutational conjecture.

## Attempts

1. **Free orbits of the relative automorphism actor.** *Covers finite stabilizers
   only* (`permutational-boone-higman-closed-under-wreath-products`).
   - The translations `x_1 -> x_1 g` act freely on `Hom_M(M * F_2, M)`, so every
     stabilizer of the input there is trivial.
   - Lamps over an infinite stabilizer `K` cannot be pushed into that set along an
     orbit. Pulling back to the free cover has infinite fibres, so supports do not
     stay finite.
2. **`X` itself carries a type (A) action of `G`.** *Covered.*
   - Suppose `G` acts on `X` faithfully, with `G` finitely presented, finitely
     generated stabilizers and finitely many orbits of pairs. Let `A ≤ Λ` with `Λ` a
     type (A) actor.
   - Then `A wr_X G ≤ Λ wr_X G`, which acts on `X × Y` with type (A) by
     `type-a-actors-closed-under-type-a-lamp-wreaths`, where `Y` is the set `Λ`
     acts on.
   - The open cases are sets that are not of this form: stabilizers that are not
     finitely generated, infinitely many orbits of pairs, or a top group acting on
     `X` through a non-finitely-presented group.
3. **Realizing `X` inside an actor set.** *Untested.* It would suffice to find a
   type (A) actor `Γ' ⊇ G` on a set `S'`, and points `s_i ∈ S'`, with
   `G ∩ Stab_(Γ')(s_i)` equal to the stabilizers of `X`. Relative automorphism actors
   with other embeddings of `M` into `Aut_M(M * F_2)` are the first candidates.
4. **Kaloujnine--Krasner.** *Does not reduce.* It embeds extensions in unrestricted
   wreath products, which are outside the restricted setting.

## First test cases

- `Z wr_(F_2/⟨a⟩) F_2`, with infinite cyclic stabilizers. The free group `F_2` is not
  of type (A) on the cosets of `⟨a⟩`, since there are infinitely many double cosets
  `⟨a⟩\F_2/⟨a⟩`.
- The wreath products `Z^d wr_(K\G) G` of arXiv:2609.01868 whose `K` is infinite and
  whose `G` is in `B_A`.
