---
rg: 2
id: free-kernel-extensions-stay-in-the-permutational-class-proof
kind: route
title: Embed G in Aut(K) × G/K through conjugation, using that K is centreless and Aut(F_r) lies in B_A
target: free-kernel-extensions-stay-in-the-permutational-class
requires:
  - aut-free-groups-satisfy-permutational-boone-higman
  - boone-higman-type-a-class-closed-under-finite-extensions
  - type-a-action-gives-boone-higman-for-subgroups
---

**Lemma (centreless-kernel embedding).** Let `K ⊴ G` with `Z(K) = 1`. Then
`Φ: G -> Aut(K) × G/K`, `g ↦ (c_g|_K, gK)` with `c_g(k) = g k g^-1`, is an injective
homomorphism.

*Proof.* `c_(gh) = c_g c_h`, so `Φ` is a homomorphism. If `Φ(g) = 1`, then `g ∈ K`
and `g` commutes with every element of `K`, so `g ∈ Z(K) = 1`. ∎

**Part 2.** `G ≤ Aut(K) × Q`. Both factors lie in `B_A`, and `B_A` is closed under
finite direct products and subgroups (`boone-higman-type-a-class-closed-under-finite-extensions`,
part 1). So `G ∈ B_A`.

**Part 1.** A free group of rank `r >= 2` has trivial centre. `Aut(F_r) ∈ B_A` by
BFFHZ Theorem A in its permutational form
(`aut-free-groups-satisfy-permutational-boone-higman`: Aut(F_n) embeds in a
finitely presented simple twisted Brin--Thompson group, and Theorem C, (ii) ⟹ (i),
places it in `B_A`). Apply Part 2.

**Products of free groups (the example in Part 2).** Let `K = F_(r_1) × ... × F_(r_s)`
with every `r_i >= 2`. Then `Z(K) = 1`. The factors are centreless and directly
indecomposable, so every automorphism of `K` permutes the factors up to automorphisms
of the factors. Hence `Aut(K)` contains `∏ Aut(F_(r_i))` with finite index, and it
lies in `B_A` by closure under finite direct products and finite-index overgroups.
(The description of `Aut` of a product of centreless indecomposable groups is
classical and is not re-derived here.)

**Part 3.** Induct on `m`. The kernel of `G_m -> G_(m-1)` is free of finite rank
`>= 2`, and `G_(m-1) ∈ B_A` by induction. Part 1 gives `G_m ∈ B_A`.

**Part 4.** The homotopy exact sequence gives
`π_2(B) -> π_1(F) -> π_1(E) -> π_1(B) -> π_0(F)`. Since `π_2(B) = 0` and `F` is
connected, it gives `1 -> π_1(F) -> π_1(E) -> π_1(B) -> 1`. Apply Part 1.

**Envelopes.** Every group in `B_A` embeds in a finitely presented simple group.
Every finitely generated one has solvable word problem
(`type-a-action-gives-boone-higman-for-subgroups`). ∎
