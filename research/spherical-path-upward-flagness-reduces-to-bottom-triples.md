---
rg: 2
id: spherical-path-upward-flagness-reduces-to-bottom-triples
kind: claim
title: Upward flagness of a spherical Deligne complex along a path order reduces to triples of bottom-type vertices and the shorter path
distinct_from:
  haettel-flag-poset-contractibility-criterion: that is a contractibility criterion for typed complexes; this is a reduction of one flag property of spherical Deligne complexes to a smaller configuration.
  huang-relative-artin-complex-structure-lemmas: that imports the poset structure and bowtie freeness; this derives an inductive reduction from them.
---

Let `Λ = s_1 ⋯ s_n` (`n ≥ 2`) be an irreducible spherical Coxeter diagram that is a path. Order
the types `ŝ_1 < ⋯ < ŝ_n` and give the vertices of the Artin complex `Δ_Λ` the induced relation
(`x < y` iff adjacent with smaller type). Let `Λ_{>1} = s_2 ⋯ s_n`, with order
`ŝ_2 < ⋯ < ŝ_n`. Suppose:

- (a) the poset of `Δ_{Λ_{>1}}` is upward flag;
- (b) any three type-`ŝ_1` vertices of `Δ_Λ` that are pairwise upper-bounded have a common upper
  bound.

Then the poset of `Δ_Λ` is upward flag. Conversely, upward flagness of `Δ_Λ` implies (a) and
(b). So, by induction along the path, upward flagness of `Δ_Λ` is equivalent to the bottom-triple
condition (b) for each of the paths `s_j ⋯ s_n`, `1 ≤ j ≤ n − 2`.

Proof in `spherical-path-upward-flagness-reduces-to-bottom-triples-proof` (lane
z1-05-artin-kpi1, 2026-09-13, unreviewed). The same induction pattern appears in the proof of
Lemma `lem:big lattice` of arXiv:2405.12068.
