---
rg: 2
id: free-group-leavitt-tensor-units-are-not-universal
kind: claim
title: Some decidable two-generated group embeds in no unit group of B ⊗ L_F2(1,2) with B a finitely presented Cantor crossed product over a free group
distinct_from:
  free-group-cantor-crossed-products-are-not-universal-hosts: that excludes a unital embedding of the group algebra k[H] into B; this excludes the far weaker injective homomorphism of H into (B ⊗ L)^x or GL_N(B ⊗ L), which may use Leavitt isometries and matrices over B, and so kills the free-group family for the units form of the Leavitt route rather than the group-algebra form.
  fixed-leavitt-hosts-cannot-be-universal-bh-containers: that excludes the single host L = F_2 ⊗ L; this excludes every B ⊗ L over every finitely presented crossed product over every free group at once.
  leavitt-tensor-unit-word-problem-reduces-to-base: that is the general transfer lemma from a zero-test bound on a class of bases; this is its first instance, with the bound supplied by the local extension property of tree SFTs.
artifacts:
  - research/artifacts/fp-crossed-product-shape-free-group-kill-2026-09-17.md
  - research/artifacts/fjc-crossed-product-leavitt-hosts-2026-09-16.md
---

**ESTABLISHED (unreviewed)** through
`free-group-leavitt-tensor-units-not-universal-proof`.

There is a two-generated group `H` with solvable word problem such that for no
`d >= 0`, no nonempty compact totally disconnected `F_d`-space `X` with
`B = LC(X, F_2) ⋊ F_d` finitely presented, and no `N >= 1`, is there an injective
homomorphism `H -> GL_N(B ⊗ L)`, where `L = L_(F_2)(1,2)`. The case `N = 1` is
`(B ⊗ L)^x`.

**Consequence for `decidable-groups-embed-in-cantor-crossed-leavitt-tensor-units`.**
The acting group `P` there can never be free, including `P = Z` and `P = 1`,
whatever the space, and regardless of simplicity, centre or K-theory. Free groups
are exactly the torsion-free virtually free groups (Stallings; remark, not used),
so the whole virtually free class is excluded from that claim. The same kill hits
step 1 of `boone-higman-via-leavitt-units-of-rigid-sft-overgroups` whenever the
overgroup `Λ` is free. It is the units-level counterpart of Attempt 4 on
`decidable-group-algebras-have-fp-cantor-crossed-hosts`: the Leavitt tensor,
matrices and Thompson-like units add only one exponential
(`leavitt-tensor-unit-word-problem-reduces-to-base`), so they buy no escape.

**Named invariant.** The local extension property of tree SFTs, which makes the
zero test of every such `B` doubly exponential. The failing step is the injective
homomorphism of the hard input.

DERIVATION
free-group-leavitt-tensor-units-not-universal-proof
