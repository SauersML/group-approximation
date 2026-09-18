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
4. **Correction to Attempt 2, and the one remaining source** (lane `bh-testcases`,
   2026-09-18).
   - Attempt 2 says no finitely presented simple group outside `B_A` is known. That is
     true only of the sources BFFHZ list, together with Lodha's group.
   - The five Titz Mite–Witzel kernels `Γ̌_i^q` (`titz-witzel-simple-kazhdan-cat0-lattices-exist`)
     are finitely presented, simple and Kazhdan. Their membership in `B_A` is open
     (`titz-witzel-lattices-satisfy-permutational-boone-higman`, routed through
     `titz-witzel-kernels-are-mif`).
   - The later sources are now covered: Amir–Lazarovich's lattices
     (`tree-by-complex-lattices-with-faithful-tree-factor-satisfy-pbh`) and Khanh's Leavitt
     unit group (`binary-leavitt-unit-group-satisfies-pbh`).
   - So the sharpest known test of (JE) is a common finitely presented simple overgroup of
     `Γ̌` and `V`, or of two distinct kernels `Γ̌_i^q`, `Γ̌_j^q'`.
5. **Γ̌ now passes; the remaining test is the Leavitt tensor unit group** (lane
   `bh-major-product`, 2026-09-18).
   - **Γ̌ is in `B_A`.** It lies in `B_A` through bh-groupoid's
     `euclidean-building-lattices-lie-in-permutational-bh-class`, wired by bh-integrate at
     de3934873 into `titz-witzel-lattices-satisfy-permutational-boone-higman`. Both are lane
     proofs, not reviewed.
   - **So the test pairs of Attempt 4 hold** (conditional on those proofs): `Γ̌` with `V`,
     and any two kernels. BFFHZ Corollary F puts free products of `B_A` groups in `B_A`.
   - **What is still open.** Among fp simple groups recorded on main, JE is open only for
     pairs involving a group not known to be in `B_A`:
     - `(L_p ⊗ L_p)^× / F_p^×`, bh-free-26's hosts, finitely presented and simple modulo the
       Khanh / Ara–Cortiñas imports;
     - the twisted integral-affine groups `W`, `W_(P,ℓ)`.
   - **Leavitt hosts among themselves.** Two groups hosted in `F_2`-Leavitt tensor unit
     groups have a common host `(B_1 ⊗ B_2 ⊗ L)^×`, where they commute, by the corner map in
     `leavitt-pair-unit-hosts-contain-their-own-squares`. That host is finitely presented and
     simple once `(B_1 ⊗ B_2) ⊗ L` passes the K-gate (K_1 = K_2 = 0).
   - **The natural next step: `(L ⊗ L)^× ∈ B_A`.** This would close JE for the whole recorded
     census except `W`. The route for `L^×` (`leavitt-pbh-via-cantor-module-affine-actor`)
     transfers step by step, with three gates:
     - **Orbits.** `L ⊗ L` acts faithfully on `M_2 = C(C x C, F_2)`, because `L ⊗ L` is simple.
       The copy of Brin–Thompson `2V` among its monomial units (sums of
       `(s_u ⊗ s_v)(t_(u') ⊗ t_(v'))` over rectangle dissections) has three orbits on `M_2`:
       `0`, `1` and the proper clopen indicators. This uses Matui's comparison with
       `H_0 = 0` for the `2V`-groupoid.
     - **(G1) the module extension is finitely presented.** `M_2 ⋊ 2V` should be the
       centralizer in `2V` of the half-swap on the first coordinate, by Part (i) of
       `cantor-module-thompson-v-product-fp-via-mmn-centralisers` with two colours. Then it is
       `F_∞` by Martínez-Pérez–Matucci–Nucinkis Corollary 4.11, whose Example 2.7(ii) and
       Remark 2.15 cover Brin's two-colour groups. Neither step is checked here.
     - **(G2) generation.** `(L ⊗ L)^×` must be generated by `2V` and finitely many
       transvections, each centralizing a subgroup of `2V` that carries finitely many cones
       onto all generators of `M_2`. That is the amalgam trick of
       `leavitt-cantor-module-fp-via-thompson-amalgam`.
     - **(G3) the unit group is finitely presented.** This is the conditional import.
