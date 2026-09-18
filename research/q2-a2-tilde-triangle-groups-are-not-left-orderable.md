---
rg: 2
id: q2-a2-tilde-triangle-groups-are-not-left-orderable
kind: claim
title: No subgroup of index at most 7 in a Fano-plane triangle group (A~_2 building of order 2) is left-orderable
distinct_from:
  higher-rank-p-adic-lattices-are-not-left-orderable: that imports Deroin–Hurtado for irreducible lattices in p-adic semisimple groups; this is a finite certificate for every simply transitive A~_2 group of order q = 2, with no linearity, arithmeticity or local-field hypothesis, so it also covers any such group on a non-Bruhat–Tits building or in characteristic 2
  irreducible-tree-product-lattices-are-not-left-orderable: that is the product-of-trees analogue of Deroin–Hurtado and is open; this is a different building type (A~_2) settled by computation
---

**ESTABLISHED (computation with a complete rewriting system).**

A *triangle presentation* over the Fano plane (Cartwright–Mantero–Steger–Zappa) is a
bijection `λ` from the 7 points to the 7 lines and a set `T` of triples of points such that
`(x,y,z) ∈ T ⇒ (y,z,x) ∈ T`, and for each pair `(x,y)` a `z` with `(x,y,z) ∈ T` exists iff
`y ∈ λ(x)`, and is then unique. The group is
`Γ_T = ⟨a_0, …, a_6 | a_x a_y a_z = 1 for (x,y,z) ∈ T⟩`.

**Statement.** Up to relabeling the points there are exactly 11 triangle presentations over
the Fano plane. Seven of them are torsion-free (no triple `(x,x,x)`). None of the 11 groups
is left-orderable, so none of them embeds in `Homeo_+(R)`. Moreover, for each of the seven
torsion-free groups, no subgroup of index at most 7 is left-orderable.

The seven torsion-free ones, by cyclic relator classes (`xyz` means `a_x a_y a_z = 1`):

| # | relators |
|---|---|
| 4 | 001 023 134 152 246 365 456 |
| 5 | 001 023 134 152 246 366 455 |
| 6 | 001 023 134 152 266 365 445 |
| 7 | 001 023 145 156 224 336 465 |
| 8 | 012 023 031 145 264 356 465 |
| 9 | 012 034 056 135 164 254 263 |
| 10 | 012 034 056 136 145 235 264 |

**Relation to the type-kernel certificate.** The worker lane `sw-108` independently certifies
(node `a2-triangle-type-kernels-q2-q3-act-trivially-on-the-line`, landing in parallel) that the
index-3 type kernel `Γ_0` of every `q = 2, 3` triangle group has no nontrivial action on the
line, which is stronger for `Γ_0` and implies the index-1 part here. What this node adds is the
remaining conjugacy classes of subgroups of index at most 7, computed by a different code base
(shortlex completion instead of a building model), so the two agree where they overlap.

**Why this matters for Navas's Question 3.** By Cartwright–Mantero–Steger–Zappa (Geom.
Dedicata 47, 1993) `Γ_T` acts simply transitively on the vertices of an A~_2 building of
order 2. The torsion-free ones are therefore uniform lattices on A~_2 buildings, which have
property (T) (Cartwright–Młotkowski–Steger, Ann. Inst. Fourier 44, 1994; also Żuk's
spectral criterion, since the link is the incidence graph of the Fano plane). They are among
the smallest explicit torsion-free Kazhdan groups, and the Deroin–Hurtado theorem does not
cover a lattice on an exotic building. This claim removes all of them as witnesses for
`infinite-left-orderable-kazhdan-group`. The Kazhdan property is context only: the
non-orderability proof uses nothing but the presentation.

**Proof shape** (full proof in `q2-a2-tilde-triangle-groups-are-not-left-orderable-proof`).

1. The 98 length-2 rules obtained from the relators by shortlex completion form a *confluent*
   rewriting system for every `Γ_T` (checked exhaustively on all critical pairs). So normal
   forms solve the word problem and every nonempty normal word is a nontrivial element.
   Sphere sizes 14, 98, 560 match the vertex counts of an A~_2 building of order 2.
2. A positive cone `P` restricted to the ball `B_r` satisfies: exactly one of `g, g^{-1}` lies in
   `P` for `g ≠ 1`, and `g, h ∈ P, gh ∈ B_r ⇒ gh ∈ P`. These clauses are unsatisfiable on `B_2`
   for groups 5–10 and on `B_3` for group 4 (two SAT solvers agree).
3. For 5, 6, 9, 10 a hand proof exists: no 2-colouring of the points avoids a monochromatic
   relator class (for 9 and 10 the classes form a Fano plane, which is not 2-colourable), and
   a relator `a_x a_y a_z = 1` with all three letters of one sign contradicts positivity.
4. For a subgroup `H` of index `d <= 7` (GAP `LowIndexSubgroupsFpGroup`, all conjugacy
   classes; left-orderability is conjugation invariant), the same clauses restricted to
   `H ∩ B_r`, with membership read off the coset permutation action, are unsatisfiable on
   `B_3`, or on `B_4` for seven of the 85 classes.

**Calibration.** The same script finds the free group `F_2`, `Z^2` and the Klein-bottle group
satisfiable on `B_4`, and `Z/3` unsatisfiable. See `experiments/a2-triangle-left-orders-2026-09-17/lo_sat_q2.out`.

**Scope.** Only order `q = 2` simply transitive A~_2 groups and their subgroups of index
`<= 7`. Deeper finite-index subgroups are not covered, and left-orderability of a subgroup
does not follow from, or imply, that of the group. Orders `q ≥ 3` are open here;
for `q = 3` the count `(q^2+q+1)(q+1)/3` is not an integer, so every triangle presentation
has torsion.
