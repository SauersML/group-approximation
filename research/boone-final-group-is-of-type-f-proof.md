---
rg: 2
id: boone-final-group-is-of-type-f-proof
kind: route
title: "Proof: glue finite classifying spaces along the tower, with a wedge of circles as the last edge space"
target: boone-final-group-is-of-type-f
requires:
  - boone-base-group-two-generator-one-relator
  - boone-hnn-tower-embeds-base-group
  - boone-base-group-and-lemma-five
  - boone-halting-lift-is-free-on-t-and-stable-letters
---

## Tool: graphs of aspherical spaces

**Scott--Wall** (P. Scott and T. Wall, *Topological methods in group theory*,
LMS Lecture Notes 36 (1979), Prop. 3.6; A. Hatcher, *Algebraic Topology*,
Thm. 1B.11). Let `Y` be a connected graph of spaces: connected CW vertex spaces
`X_v` and edge spaces `X_e`, with each edge space glued by `X_e x [0,1]` to its
two end vertex spaces through maps `f_e^0, f_e^1` that are injective on `pi_1`.
If all `X_v` and `X_e` are aspherical, the total space is aspherical, and its
fundamental group is the fundamental group of the corresponding graph of groups.

**Finiteness.** If each `X_v`, `X_e` is a finite CW complex and the `f_e^j` are
cellular, the total space is a CW complex whose cells are the cells of the
`X_v` and the products `sigma x (0,1)` for cells `sigma` of the `X_e`; so it is
finite, of dimension `max(dim X_v, dim X_e + 1)`.

**Realizing homomorphisms.** For a connected CW complex `K` and an aspherical
CW complex `Y`, every homomorphism `pi_1(K) -> pi_1(Y)` is induced by a
basepoint-preserving map (Hatcher Prop. 1B.9), which cellular approximation
makes cellular rel the base vertex.

## Step 0. The base group

`G = <t, x, y | [x,y]>` ([[boone-base-group-two-generator-one-relator]]) is
`Z * Z^2`. Its presentation complex `K_G = S^1 v T^2` (one vertex, three edges,
one 2-cell) is aspherical: it is a graph of spaces with vertex spaces `S^1`,
`T^2` and a point as edge space, so Scott--Wall applies (equivalently, its
universal cover is a tree of planes and lines, contractible).

## Step 1. The tower `G'_M` has a finite 3-dimensional `K(pi,1)`

By [[boone-hnn-tower-embeds-base-group]], `G'_M` is obtained from `G` by adjoining
stable letters `r_1..r_n` (finitely many: one per residue pair below the modulus
carrying a quadruple), where `r_i` conjugates `A_i = G_{ab}^{mm}` onto
`B_i = G_{c0}^{m^2,1}` or `G_{0c}^{1,m^2}` by `phi_i = emb_B o emb_A^{-1}`, and
`emb_A, emb_B : G -> G` are injective endomorphisms with ranges `A_i, B_i`
(`emb_injective`, `Gsub` is the range of `emb`, [[boone-base-group-and-lemma-five]]).
Since each stage's associated subgroups are images of subgroups of `G` under the
injective map `iota` from `G`, the iterated tower is the multiple HNN extension
of `G` with these letters (the presentations agree: generators of `G` plus
`r_i`, relators of `G` plus `r_i a r_i^{-1} = phi_i(a)`).

Take the graph of spaces with one vertex space `K_G`, and `n` loop edges with edge
space `K_G`, glued by cellular maps `f_i^0, f_i^1 : K_G -> K_G` inducing
`emb_A` and `emb_B` on `pi_1`. Both are injective. The fundamental group of the
graph of groups is `< G, r_i | r_i emb_A(g) r_i^{-1} = emb_B(g) >`, the multiple HNN
extension above. By Scott--Wall and finiteness, `X' = K(G'_M, 1)` is a finite CW
complex of dimension 3.

## Step 2. The final group

`G_M = FinalGroup M` is the HNN extension of `G'_M` with associated subgroups both
equal to `L = <t>' = <t, r_1, ..., r_n>` and the identity isomorphism. By
[[boone-halting-lift-is-free-on-t-and-stable-letters]], `L` is free on
`t, r_1, ..., r_n`, so `K(L,1)` is the wedge `W` of `n + 1` circles, a finite
1-dimensional complex. Take the graph of spaces with vertex space `X'`, one loop
edge with edge space `W`, and `f^0 = f^1 : W -> X'` a cellular map inducing the
inclusion `L -> G'_M` (injective). Its fundamental group is
`< G'_M, k | k l k^{-1} = l, l in L >`, which is `G_M`. By Scott--Wall and
finiteness, the total space is a finite 3-dimensional `K(G_M,1)`.

## Conclusion

`G_M` has a finite `K(G_M,1)`, so it is of type `F`, hence of type `F_n` for all
`n`, and `gd(G_M) <= 3`. Nothing about the machine beyond the finiteness of its
quadruple table and the freeness of `L` is used.

**Where finite presentability alone would not suffice.** The HNN extension of a
type-`F` group along a finitely generated subgroup that is not of type `F_2` is
never of type `FP_3` (the Mayer--Vietoris sequence forces the edge group to be
`FP_2` once the total group and vertex group are `FP_3`; R. Bieri, *Homological
dimension of discrete groups*, 1981, Prop. 2.13). This remark is not used in the
proof. The classical
Mikhailova-style constructions stop at `F_2` exactly there. The freeness of
`<t>'` is what removes that obstruction for the Aanderaa--Cohen tower.
