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

## Attempts

1. **The hard test pair: a Kazhdan Kac--Moody lattice and `V`.** *Holds.* Let `Λ` be
   a finitely presented simple non-affine Kac--Moody group over a finite field
   [CR09], Kazhdan or not. By `fp-simple-kac-moody-lattices-satisfy-pbh` (Rybak's MIF
   theorem plus BFFHZ Theorem C), `Λ ∈ B_A`, and `V ∈ B_A`. So `Λ * V ∈ B_A`
   by BFFHZ Corollary F, and `Λ * V` lies in a finitely presented simple group.
2. **Every listed source passes.** BFFHZ (arXiv:2503.21882v2, l.762--767, quoted in
   `fp-simple-kac-moody-lattices-are-highly-transitive`) write that non-affine
   Kac--Moody groups are "the only existing source of finitely presented infinite
   simple groups for which PBH remains open". Those are now in `B_A`, and so is
   Lodha's circle group (`lodha-circle-group-satisfies-pbh`), which that sentence
   omits. So (JE) holds for every pair drawn from the sources BFFHZ list, together
   with Lodha's group. Since `B_A` is closed under finite direct products and
   commensurability, the self-closures (SQ), (FZ) and (FW) of
   `bh-class-free-products-iff-joint-embedding-and-free-z` and
   `bh-class-finite-extensions-reduce-to-finite-simple-wreaths` hold for them too.
   *Consequence:* a counterexample to (JE), or to any of the closure properties
   reduced to it, needs a finitely presented simple group outside `B_A`, and none is
   known. This is a literature-status remark, not a theorem about all finitely
   presented simple groups.
3. **FFWZ abstract twisted Brin--Thompson groups do not give (JE) outright.**
   - Let `S` and `T` be finitely presented simple. By FFWZ Theorem C (arXiv:2603.24687v2,
     l.1199--1200) each sharply embeds in `(A_i, K_i)` for a type [A_2] action with
     kernel `K_i`.
   - The product actor `A = A_1 x A_2` on `X_1 ⊔ X_2` is of type [A_2], so `SV_A` is
     finitely presented and relatively simple with largest normal subgroup `SK_A`
     (FFWZ Theorems A and B). `S` and `T` embed in it meeting `SK_A` trivially (the
     computation of `research/artifacts/bh-simple-products-embed-2026-09-12.md` §1).
     So does `V`: it is simple, and it is not inside `SK_A`, whose elements induce the
     identity permutation on leaves.
   - Hence the simple quotient `SV_(A/K)` contains `S`, `T` and `V`. It is finitely
     generated, but by FFWZ Corollary 4.2 it is finitely presented iff
     `A/K = A_1/K_1 x A_2/K_2` is.
   - So FFWZ gives (JE) in finitely generated simple groups, and the gap to finite
     presentation is exactly the relBH-to-BH gap: the second part of FFWZ
     Question 5.9 (`fp-relatively-simple-pairs-embed-with-fng-kernels`), or finite
     presentation of each `A_i/K_i`. When `A_i/K_i` is finitely presented, its
     faithful action is of type (A) and `S ∈ B_A` already. *Stops* at that gate.
