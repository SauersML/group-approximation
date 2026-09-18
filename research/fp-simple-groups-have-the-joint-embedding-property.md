---
rg: 2
id: fp-simple-groups-have-the-joint-embedding-property
kind: claim
title: Any two finitely presented simple groups embed in a common finitely presented simple group
distinct_from:
  boone-higman-closed-under-finite-direct-products: that asks for S x T inside a finitely presented simple group; this asks only that S and T embed separately in one common host, which products imply.
  bh-class-free-products-iff-joint-embedding-and-free-z: that proves free-product closure equivalent to this statement plus one self-closure; this is the statement itself.
artifacts:
  - research/artifacts/gq-bh-bh-permanence-closure-reductions.md
---

**OPEN.** (JE): for finitely presented simple `S` and `T` there is a finitely
presented simple `U` with `S <= U` and `T <= U`. Equivalently, the class `𝓑` of
groups embedding in finitely presented simple groups is directed: any two members
embed in one finitely presented simple group.

**Where it sits.**
- It follows from `boone-higman-conjecture` (`S x T` is finitely presented with
  solvable word problem), from closure of `𝓑` under finite direct products, and from
  closure of `𝓑` under free products.
- It is the common core of three closure questions:
  - direct products ⟺ (JE) ∧ (SQ) (Attempt 10 of
    `boone-higman-closed-under-finite-direct-products`);
  - free products ⟺ (JE) ∧ (FZ) (`bh-class-free-products-iff-joint-embedding-and-free-z`);
  - direct products and finite extensions ⟺ (JE) ∧ (FW)
    (`bh-class-finite-extensions-reduce-to-finite-simple-wreaths`).
- It holds for groups with the permutational property: if `S, T ∈ B_A` then
  `S * T ∈ B_A` (BFFHZ Corollary F, imported in
  `aut-free-groups-satisfy-permutational-boone-higman`), so a common envelope exists.

No attempt at a general proof is recorded yet. A natural first test: two
finitely presented simple groups of very different kinds, e.g. a Kazhdan
Kac--Moody lattice and Thompson's `V`.
