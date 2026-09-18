---
rg: 2
id: free-permutational-products-preserve-pbh
kind: claim
title: Free permutational products (*_X K) ⋊ W over W-sets with finite stabilizers stay in the permutational Boone--Higman class, so do HNN extensions and amalgams X *_C (C x K) over finite C with no retraction
distinct_from:
  aut-free-groups-satisfy-permutational-boone-higman: that imports BFFHZ Corollary F, free products K * W, which is the case of a free W-set here; this allows W-sets with finite point stabilizers.
  pbh-class-closed-under-graph-products: that realizes X *_C (C x K) when C is a retract of X, for C of any size; this needs no retraction, but needs C finite (or the lamp wreath over X/C in B_A).
  pbh-class-closed-under-common-retract-amalgams: that amalgamates over common retracts; this amalgamates over finite subgroups that are retracts of neither side.
  permutational-boone-higman-closed-under-wreath-products: that is the abelian-base analog, lamps A^(X) ⋊ W; this is the free-product base *_X K, and it uses that theorem as its input.
  bh-embeddability-survives-decidable-edge-hnn: that is the open HNN permanence over finitely generated decidable edges for embeddability into fp simple groups; this settles the centralizing case over finite edges in the permutational form.
artifacts:
  - research/artifacts/gq-bh-bh-free-10-free-permutational-products.md
---

**ESTABLISHED** by `free-permutational-products-preserve-pbh-proof` (lane proof,
not reviewed; no priority claimed). `B_A` is the class of groups that embed in a
group admitting an action of type (A)
(`boone-higman-type-a-class-closed-under-finite-extensions`).

## Statement

Let `W, K ∈ B_A`, and let `X` be a countable `W`-set. Write
`K *_X W = (*_(x ∈ X) K_x) ⋊ W` for the free permutational product. Here `K_x` is a
copy of `K`, and `w` sends `k_x` to `k_(wx)`, the same element of `K` in the factor
at `wx`.

1. **Criterion.** If `Z/2 wr_X W ∈ B_A`, then `K *_X W ∈ B_A`.
2. **Finite stabilizers.** If every point stabilizer of `X` is finite, then
   `K *_X W ∈ B_A`. This is part 1 together with
   `permutational-boone-higman-closed-under-wreath-products`.
3. **Centralizing amalgams over finite subgroups.** For `W, K ∈ B_A` and a finite
   subgroup `C <= W`, the amalgam `W *_C (C × K) = <W, K | [c, k] = 1 (c ∈ C, k ∈ K)>`
   lies in `B_A`. With `K = Z` this is the centralizing HNN extension
   `<W, t | t c t^(-1) = c (c ∈ C)>`. No retraction `W -> C` is needed.
4. **Amalgams over finite subgroups.** Let `X, Y ∈ B_A` and let `C` be a finite group
   with embeddings `C -> X` and `C -> Y`. Then `X *_C Y ∈ B_A` iff there are a group
   `M ∈ B_A` and embeddings `X -> M`, `Y -> M` that agree on `C`. In particular every
   double `X *_C X` over a finite subgroup lies in `B_A`.
5. **HNN extensions over finite subgroups.** Let `W ∈ B_A` and let `θ: C_1 -> C_2` be
   an isomorphism between finite subgroups. Then `W *_θ ∈ B_A` iff `W` embeds in some
   `M ∈ B_A` in which `θ` is conjugation by an element of `M`.

So everything here lies in `B_A`, embeds in a finitely presented simple group, and
has solvable word problem if it is finitely generated
(`type-a-action-gives-boone-higman-for-subgroups`).

## Examples

- `<V, t | t c t^(-1) = c>` for an involution `c` of Thompson's group `V`, and every
  double `V *_F V` over a finite subgroup `F <= V`. `V` is simple, so `F` is not a
  retract and the common-retract closure does not apply. `V` has no finite quotients,
  so the finite-index argument for residually finite factors does not apply either.
- `V *_(Z/2) (Z/2 × Aut(F_n))` and similar centralizing amalgams of fp simple MIF
  groups with anything in `B_A`.
- The free permutational products `K *_(W/C) W` for any finite `C <= W`. With
  `X = W` free this is BFFHZ Corollary F, since `K *_W W ≅ K * W`.

## Scope

- **What remains of amalgams and HNNs over finite subgroups** is the conjugacy step in
  parts 4 and 5: identifying two finite subgroups of `B_A`-groups, compatibly with a
  given isomorphism, inside a common `B_A`-overgroup. It is automatic for doubles and
  for centralizing extensions. For residually finite `X, Y` it also follows from
  finite-index closure and free products. No general argument is known here.
- **Infinite edges.** Part 1 turns centralizing amalgams over an infinite `C` into the
  lamplighter `Z/2 wr_(W/C) W`. That lamplighter has solvable word problem only when
  membership in `C` is decidable
  (`pbh-wreath-closure-fails-over-undecidable-stabilizers`). The decidable case is the
  open claim `pbh-closed-under-decidable-permutational-wreaths`.
- **Twisted factors.** Point stabilizers act trivially on their factor `K_x` here.
  Free permutational products in which `Stab(x)` acts on `K_x` by automorphisms are
  not covered.
