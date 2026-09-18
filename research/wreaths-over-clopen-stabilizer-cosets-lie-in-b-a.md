---
rg: 2
id: wreaths-over-clopen-stabilizer-cosets-lie-in-b-a
kind: claim
title: Permutational wreath products over the coset space of a clopen stabilizer inside a finitely presented full clopen-transitive Cantor host lie in the permutational class B_A
distinct_from:
  type-a-actors-closed-under-type-a-lamp-wreaths: that needs the top group to act on the wreath set itself with type (A); here the top group G is an arbitrary subgroup of the host, need not be finitely presented, and acts on G/H with infinitely many pair orbits and possibly non-finitely-generated stabilizers.
  permutational-boone-higman-closed-under-wreath-products: that covers G-sets with finite point stabilizers through free orbits of relative automorphism actors; this covers G-sets whose point stabilizers are commensurated-above clopen stabilizers, which are typically infinite.
  pbh-closed-under-decidable-permutational-wreaths: that is the open general closure over G-sets with decidable stabilizers; this proves the case where the stabilizer is commensurated-above a clopen stabilizer in a full host.
artifacts:
  - research/artifacts/gq-bh-openq-papers-list.md
---

**ESTABLISHED** by `wreaths-over-clopen-stabilizer-cosets-proof` (lane proof,
elementary; not independently reviewed; no priority claimed).

## Statement

Let `Y` be a Cantor space and `D ≤ Homeo(Y)` a finitely presented full
clopen-transitive Cantor host, in the sense of
`fp-clopen-transitive-full-cantor-groups-have-type-a-actions`. Let `G ≤ D`, let
`U ⊂ Y` be a proper nonempty clopen set with setwise stabilizer
`K = Stab_G(U) = {g ∈ G : g(U) = U}`, and let `H ≤ G` be a subgroup with

    K ≤ H   and   [H : K] < ∞.

Then for every group `L` in the permutational class `B_A`, the restricted
permutational wreath product `L ≀_{G/H} G = L^(G/H) ⋊ G` lies in `B_A`. If `L` and
`G` are finitely generated, it embeds in a finitely presented simple group.

## What it adds

- Nothing is assumed about `G` beyond `G ≤ D`: `G` need not be finitely presented,
  `H` need not be finitely generated, and `G` may have infinitely many orbits on
  pairs of `G/H`. These are exactly the cases left open by Attempt 2 of
  `pbh-closed-under-permutational-wreaths-with-infinite-stabilizers` (refuted as stated by
  `pbh-wreath-closure-fails-over-undecidable-stabilizers`; the corrected open form is
  `pbh-closed-under-decidable-permutational-wreaths`, of which this is a proved case).
- The only input is *geometric*: the coset space must be realized, up to finite
  covers, as an orbit of clopen sets. Attempt 3 of that node asked for exactly such a
  realization inside a type (A) actor; here the actor is the clopen action of `D`.

## Applications

- `lamp-wreaths-over-psl2-tree-vertices-lie-in-b-a`: `L ≀_X PSL_2(Z[1/2])` with `X` the
  vertices of one type of the Bruhat–Tits tree. This is the group of
  Almeida–Dantas–Oliveira-Tosti, arXiv:2609.01868.
- `lamp-wreaths-over-cyclic-cosets-of-f2-lie-in-b-a`: `L ≀_{F_2/⟨a⟩} F_2`, the first test
  case of `pbh-closed-under-decidable-permutational-wreaths`.
- `double-of-psl2-z-half-along-psl2-z-lies-in-b-a`: with `free-permutational-products-preserve-pbh`,
  the non-residually-finite double `PSL_2(Z[1/2]) *_{PSL_2(Z)} PSL_2(Z[1/2])` lies in `B_A`.
