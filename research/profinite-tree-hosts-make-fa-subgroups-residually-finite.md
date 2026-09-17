---
rg: 2
id: profinite-tree-hosts-make-fa-subgroups-residually-finite
kind: claim
title: In a group acting faithfully on locally finite trees every subgroup with property FA is residually finite, so tree and self-similar engines cannot prove HNN permanence of Boone--Higman embeddability
distinct_from:
  finite-index-edge-hnn-embeds-in-fp-simple-group: that records, in (L1) and (L4), that the vertex groups of one given faithful Bass--Serre tree are residually finite; this bounds every host of an input at once, through its subgroups with property FA, so enlarging the input first cannot repair it.
  bliw-locally-finite-tree-actions-embed-in-fp-simple-groups: that imports the tree embedding theorems and mentions, without proof, that vertex stabilizers are residually finite; this proves that for products of trees, transfers it to every subgroup with property FA and draws the exclusion of whole classes of inputs from every host of the theorems.
  fa-subgroups-of-graph-towers-lie-in-base-pieces: that places FA subgroups of iterated HNN and amalgam towers in base groups, with no local finiteness; this uses local finiteness and faithfulness to make FA subgroups residually finite in every host, towers or not.
  baumslag-gersten-base-is-elliptic-in-every-tree-action: that forces one non-FA subgroup, BS(1,n) in the Baumslag--Gersten group, to be elliptic and excludes hosts with BS-free vertex groups; this excludes hosts with faithful locally finite actions for every input containing an infinite non-residually-finite FA subgroup.
  atiyah-permanence-closure-kazhdan-subgroups-are-rf: that shows Kazhdan subgroups of the Strong Atiyah permanence closure are residually finite; this shows FA subgroups of groups acting faithfully on locally finite trees are residually finite, a host-geometry statement with no permanence closure.
  product-of-trees-lattices-satisfy-permutational-boone-higman: that is the open membership of product-of-trees lattices in the permutational class; this shows such lattices contain no infinite subgroup with property FA.
artifacts:
  - research/artifacts/profinite-tree-hosts-fa-subgroups-rf-proof-attempt-2026-09-17.md
---

**OPEN.** The route `profinite-tree-hosts-fa-subgroups-rf-proof` was withdrawn on
2026-09-17 after two referees refuted Item 3, host (E4), and its lattice coverage
claim. See `## Attempts`.

Let `L` act on locally finite trees `T_1, ..., T_m` (`m >= 1`), each factor
preserved, and suppose only the identity acts trivially on all of them.

1. **Profinite stabilizers.** For vertices `v_i` of `T_i`, the common stabilizer
   `L_(v_1) ∩ ... ∩ L_(v_m)` is residually finite.
2. **FA subgroups.** Every subgroup `H <= L` with Serre's property FA is
   residually finite. If some `T_i` has finite vertex stabilizers, `H` is finite,
   and for that conclusion faithfulness is not needed.
3. **Hosts excluded.** Let `K` contain an infinite subgroup `H` with property FA
   that is not residually finite, for instance an infinite simple group with
   property FA. Then `K` is a subgroup of none of the following hosts:
   - **(E1)** a group acting faithfully on a locally finite tree, which is the
     hypothesis of Theorem B of Bux--Llosa Isenrich--Wu;
   - **(E2)** the fundamental group of a finite graph of groups with finite-index
     edge inclusions that acts faithfully on its Bass--Serre tree, which is the
     hypothesis of their Theorem 10.5, of
     `finite-index-edge-hnn-embeds-in-fp-simple-group`, and of the faithful
     enlargement in their Theorem 11.1;
   - **(E3)** a group of automorphisms of a locally finite rooted tree, in
     particular a finitely presented self-similar group as in
     `fp-self-similar-groups-embed-in-fp-simple-groups`;
   - **(E4)** a group acting, factor by factor, on a finite product of locally
     finite trees with finite vertex stabilizers in some factor, which covers
     the factor-preserving lattices of
     `product-of-trees-lattices-satisfy-permutational-boone-higman`.
4. **Consequence for the HNN permanence.** Let `q >= 4` be a prime power and
   `S_q` the finitely presented simple Kazhdan group of
   `km-246-lattice-fp-simple-kazhdan-irs-rigid-for-q-ge-4`. Every input
   `(A, C_1, C_2, phi)` of `bh-embeddability-survives-decidable-edge-hnn` with
   `S_q <= A` has `A*_phi` in none of the hosts (E1)--(E4). This includes
   `S_q * Z` (trivial edges) and the mapping tori `S_q ⋊_phi Z` (edges
   `C_1 = C_2 = S_q`). So no proof of that claim can pass through embedding
   `A*_phi`, or any overgroup of it, in such a host. Those engines can at best
   prove its restriction to inputs whose FA subgroups are all residually finite.
5. **Calibration: the invariant stops the engines, not the claim.** Let `S` be
   a finitely presented simple MIF group, for instance `S_q`, and let
   `phi in Aut(S)`. Then both `S * Z` and `S ⋊_phi Z` lie in the permutational
   Boone--Higman class `B_A` of
   `boone-higman-type-a-class-closed-under-finite-extensions`. Hence both embed
   in finitely presented simple groups. So for finitely presented simple MIF
   bases, the claim holds for trivial edges and for the edges `C_1 = C_2 = S`.

## The invariant and where each engine dies

The invariant is the finite residual of a subgroup with property FA. In a host
of type (E1)--(E4), the finite residual is trivial. In `S_q` it is all of `S_q`.
Every engine dies at the same step, placing the input inside the host. There
`S_q` fixes a vertex of each subdivided factor, so it lands in a profinite
stabilizer, and a simple subgroup of a residually finite group is finite.

This rules out enlarging the input first. Theorem 11.1 of Bux--Llosa
Isenrich--Wu glues extra vertex groups to make an action faithful, and every
such move produces another host of type (E1) or (E2).

## What it does not touch

- **Type (A) engines survive.** These are twisted Brin--Thompson groups, the
  actor `Aut_S(S * F_n)` and its enlargements, and the stable-permutation
  extension of Attempt 6 of `bh-embeddability-survives-decidable-edge-hnn`.
  Item 5 uses them.
- **Free bases.** The routes `oriented-artin-bh-via-free-group-hnn-permanence`
  and `magnus-hnn-permanence-from-decidable-edge-permanence` only need free or
  one-relator bases. For free bases the obstruction says nothing: by
  `fa-subgroups-of-graph-towers-lie-in-base-pieces` every FA subgroup of `A*_phi`
  is conjugate into `A`, and a free group acts freely on its Cayley tree, so its
  FA subgroups are trivial. Whether some one-relator group contains
  an infinite non-residually-finite FA subgroup is not addressed.
- **Groups generated by elliptic elements.** The same proof covers a finitely
  generated subgroup all of whose elements fix vertices, by Serre, *Trees*,
  §I.6.5, Corollary 3. That variant is not needed here.

## Attempts

- 2026-09-17 audit (`swarm-0917`): route `profinite-tree-hosts-fa-subgroups-rf-proof`
  (subdivide, fix a vertex, restrict to finite balls, separate the Kac--Moody input
  by its finite residual), held OPEN. The route was withdrawn to
  `research/artifacts/profinite-tree-hosts-fa-subgroups-rf-proof-attempt-2026-09-17.md`,
  which keeps the full proof text. Both lenses refuted Item 3, host (E4). Their
  reasons, verbatim:
  * **Lens 1 (refuted).** The first step that fails is in Item 3, host (E4). The statement says (E4) "covers the factor-preserving lattices of product-of-trees-lattices-satisfy-permutational-boone-higman". The prerequisite that defines those lattices is product-of-trees-lattices-with-faithful-factor-satisfy-pbh. There Gamma acts on X = T_1 x ... x T_n with finite stabilizers of vertices of the product X. It may also have nontrivial kernels K_i on each factor, and faithfulness on X is only an extra hypothesis in its item 4. (E4) needs something stronger: finite vertex stabilizers in some single factor T_i. Lattices usually fail that. For example, F_2 x F_2 acting on T_4 x T_4 has stabilizer {1} x F_2 for a vertex of the first factor, and that group is infinite. So the route's (E4) step, which only uses the finite-stabilizer part of Item 2, does not apply to these lattices. The general part of Item 2 does not help either, since it needs faithfulness, which the lattice definition does not give. The route never proves the lattice coverage, and the same goes for the distinct_from sentence "this shows such lattices contain no infinite subgroup with property FA". The conclusion is probably true by another argument. An FA subgroup fixes a vertex in each subdivided factor, so it fixes a cell of X, and a cell stabilizer is finite. But that argument is not written anywhere. The rest checks out. Step 0 and Items 1 and 2 are fine. (E1)-(E3) are fine, including the Serre valence formula and BLIW Theorem B/10.5 hypotheses, which are cited verbatim in the bliw claim. Item 4 correctly uses km-246 (infinite, finitely presented, simple, property (T)), Watatani (T implies FA) and Britton's lemma. Item 5 matches its imports: Theorem C (iv)=>(i), Corollary F (free products), (O) with Q=Z and an injective map into Out(S), the centre computation for z = t^m s_0^-1 and its index m, and items 1-3 of the B_A closure claim. Verdict posted on the bus (verdict a9e76978).
  * **Lens 2 (refuted).** Items 1, 2, (E1), (E2), (E3), 4 and 5 check out. Step 0 (subdivision) is correct, the ball-restriction residual finiteness is correct, the Bass-Serre valence count is correct, and the case (ii) central element z = t^m s_0^-1 computes correctly. The prerequisites say what is used: BFFHZ Theorem C (iv)=>(i), Corollary F, outer-extension (O), closure of B_A under subgroups, products and finite-index overgroups, and Rybak MIF for S_q. The failing step is Item 3 (E4), both its statement and its proof. (E4) is defined as a group acting factor by factor on a product of trees "with finite vertex stabilizers in some factor", and the claim says this "covers the factor-preserving lattices of product-of-trees-lattices-satisfy-permutational-boone-higman". That is false. Those lattices (setting of product-of-trees-lattices-with-faithful-factor-satisfy-pbh) have finite stabilizers of vertices of the PRODUCT X = T_1 x ... x T_n. The stabilizer of a vertex in a single factor is typically infinite. Examples: F_2 x F_2 on T_4 x T_4; any BMW or Burger-Mozes lattice, where Gamma_(v_1) acts simply transitively on V(T_2). The parent node itself says the Gamma_0-stabilizers of T_i-vertices are lattices in the other factors. So (E4) as stated covers essentially none of these lattices. These lattices also need not act faithfully on X (only finite kernel), so Item 1 / Item 2 (RF part), which need faithfulness, don't apply to them either. The exclusion conclusion for these lattices is still true: an FA subgroup H fixes a vertex w_i of each subdivided factor, so H stabilizes a cell of X, and that stabilizer is finite, so H is finite. But no step of the route proves this. The route's (E4) argument only invokes the factor-wise finite-stabilizer part of Item 2, which does not hold for these lattices. So the stated result is less general than claimed, and the coverage assertion in item 3 is unproven and literally false as worded.
