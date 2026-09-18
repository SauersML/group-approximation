---
rg: 2
id: left-preserving-local-richness-wrappers-are-affine-ug-merges
kind: claim
title: A 2-to-1 wrapper that keeps the left labels, is locally complete over affine intended classes and has pair-uniform matchings is a right merge of an affine unique game on the same left vertices, so its hardness is that game's hardness
invalidates:
  - rich-2to1-via-left-preserving-local-wrappers
distinct_from:
  linear-view-unique-verifiers-collapse-to-quotient-coarsening: that covers verifiers whose output is a unique game read through affine views of an outer label; this covers 2-to-1 outputs that keep the source left labels verbatim and add arbitrary right vertices, and its invariant is the agreement subgroup of the local intended class plus the richness mass bound, giving a translation-or-merge dichotomy rather than an exact-triple threshold.
  edge-conjugation-of-2to1-constraints-is-pure-gauge: that is a per-edge relabeling identity; this classifies every locally complete right vertex, whatever its constraints, and bounds the value of the whole output game by a unique game.
  unique-constraints-orient-at-most-half-of-a-fiber: that forbids simulating a 2-to-1 merge by unique constraints; this runs the other way, showing that the rich right vertices a local wrapper can add are unique games merged by one 2-to-1 map.
  sd-rich-and-unique-games-sos-gaps-interconvert: that proves the BKM right merge turns unique games into rich 2-to-1 games; this shows every left-preserving affine-local wrapper with pair-uniform matchings is essentially that merge, so it cannot supply a new hardness source.
artifacts:
  - experiments/rich-2to1-local-wrappers-2026-09-17/check_wrappers.py
---

**ESTABLISHED.** Fix `k >= 2`.

*Wrapper.* A **left-preserving affine-local wrapper** `W` maps a source instance
`G` to a weighted 2-to-1 game `W(G)`:

* The left vertices `U` are those of `G`, possibly duplicated. Each alphabet
  `Sigma_u` is an `F_2`-affine space with `2k` points, and the wrapper keeps it.
* The right vertices `z` are arbitrary. Each has a neighbour set `S_z`, 2-to-1
  constraints `h_(uz) : Sigma_u -> [k]` and edge weights `w_(uz) > 0`.
* Each `z` has a **local intended class**: a finite `F_2`-affine space `A_z`
  with affine surjections `r_(uz) : A_z -> Sigma_u` for `u in S_z`.
* The motivating model is folded Grassmann incidence. There `A_z` is the space of
  affine functionals on the span of the subspaces in `S_z` that obey the local
  folding equations, and `r_(uz)` is restriction. This claim says nothing about
  the internals of any particular published instance.

*Hypotheses.*

* **(LC) Local completeness.** For every `f in A_z` there is one `c in [k]` with
  `h_(uz)(r_(uz) f) = c` for all `u in S_z`. This is a property of the local
  gadget, so it holds on NO instances too.
* **(R2) Pair-uniform matchings.** At every left vertex `u`, draw an edge
  `(u,z)` with probability proportional to `w_(uz)`, and take the pairing of
  `Sigma_u` into the fibres of `h_(uz)`. Any fixed pair is a block with
  probability `1/(2k-1)`. Any two fixed disjoint pairs are both blocks with
  probability `1/((2k-1)(2k-3))`. Richness, which is the uniform law on all
  pairings, implies (R2), and so does `t`-wise uniformity for any `t >= 2`.

*Theorem.* Write `dr` for the linear part of `r`.

1. **Agreement subgroup.** Let `B_z = sum_(u in S_z) ker dr_(uz)`. Under (LC),
   `h_(uz)` is constant on the cosets of `dr_(uz)(B_z)`. So
   `|dr_(uz)(B_z)|` is 1 or 2.
2. **Dichotomy.** Every right vertex `z` falls into exactly one of two types. No
   mixed type exists.
   * **(A) Translation type.** `|B_z| = 2 |ker dr_(uz)|` for every `u`. Every
     `h_(uz)` pairs `x` with `x + b_(uz)`, where `{0, b_(uz)} = dr_(uz)(B_z)`.
   * **(D) Merge type.** `ker dr_(uz) = B_z` for every `u`. There are affine
     bijections `phi_(u'u)` with `r_(uz) = phi_(u'u) o r_(u'z)` and
     `h_(u'z) = h_(uz) o phi_(u'u)`.
3. **Mass bound.** Under (R2) the total edge mass at type-(A) vertices is at most
   ```text
   alpha_k = (4k - 5) / ((2k - 1)(2k - 3))      (about 1/k),
   ```
   so `w(D) >= 1 - alpha_k`. Under full richness the translation pairings have
   probability `(2k-1)/(2k-1)!!`.
4. **Value floor.** Let `U_W(G)` be the unique game on `U` with alphabets
   `Sigma_u`. Draw `z` from the edge mass restricted to type (D). Draw `u_0` and
   `u` independently from the neighbour law `nu_z(u) = w_(uz) / w_z`. Accept iff
   `L_u = phi_(u_0 u)(L_(u_0))`. For every left labeling `L`,
   ```text
   val_W(L) >= w(D) * val_(U_W)(L),   hence   val(W(G)) >= (1 - alpha_k) val(U_W(G)).
   ```
5. **Certificate completeness.** Call `z` *certified* by `L` if some `f in A_z`
   has `r_(uz) f = L_u` for all `u in S_z`. Suppose the uncertified right
   vertices carry edge mass `beta`. Then `val_W(L) >= 1 - beta` and
   `val_(U_W)(L) >= 1 - beta/(1 - alpha_k)`.
6. **Collapse.** Suppose a wrapper of this class proves
   `Gap-2-to-1(1 - beta, s)` hard from a source problem, and its completeness
   proof exhibits certified labelings. Then the map `G -> U_W(G)` proves
   `Gap-UG(1 - beta/(1 - alpha_k), s/(1 - alpha_k))` hard from the same source,
   with alphabet `2k` and affine permutation constraints. This map runs in
   polynomial time, because `B_z`, the type of `z` and `phi` come from linear
   algebra.

`U_W` includes the identity self-loops `u_0 = u`. These are unique constraints
too, and on NO instances their mass is at most `s/(1 - alpha_k)` anyway.

**Where the class dies.**

* **Invariant.** The agreement subgroup `B_z`.
* **Step.** A 2-to-1 map can absorb only a coset of size 2, so (1) forces the
  dichotomy. Richness then leaves translation pairings at most `alpha_k` of the
  mass. The remaining right vertices are exactly BKM Appendix B merges
  `(v, sigma)` of the unique game `U_W`.
* **Consequence.** Every wrapper in the class is transparent. It produces rich
  2-to-1 hardness only on sources where near-1 UG hardness of `U_W(G)` is
  already available, and that is UGC for those instances. The richness layer
  contributes a factor `1 - alpha_k` and nothing else.
* **Covered cases.** Right compression, right merging, auxiliary right vertices
  added over an existing left side, and "refining" the proved Grassmann 2-to-1
  instances. There the original codim-1 edges are type (A), so they carry
  `F_lin` pairings, and any rich mass must be type (D).

**Survivors.** These are not covered.

* **(G1)** Wrappers that re-encode left labels, such as long-code or composition
  encodings, or other non-affine views. That is BKM's own route, handled by
  `derived-unique-game-lower-bounds-the-noise-test` when matchings are learnable.
* **(G2)** Completeness proofs whose YES labelings satisfy the constraints
  without one common local certificate `f in A_z`.
* **(G3)** Non-affine local intended classes. Lemma (1) still gives an agreement
  partition, but its classes need not be cosets, and a mixed type is not ruled
  out.
* **(G4)** Richness at only part of the left mass. If (R2) fails on mass
  `gamma`, the bound becomes `w(D) >= 1 - gamma - alpha_k`.

This neither proves nor refutes UGC or the Rich 2-to-1 Conjecture.

DERIVATION left-preserving-local-wrappers-collapse-proof
