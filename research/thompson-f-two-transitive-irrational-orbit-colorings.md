---
rg: 2
id: thompson-f-two-transitive-irrational-orbit-colorings
kind: claim
title: A point stabilizer of a 2-transitive action of Thompson's group F is the part-wise stabilizer of its own orbit partition of an irrational F-orbit, and the disagreement set is a Cantor set exactly when it is transitive on some irrational orbit
distinct_from:
  thompson-f-two-transitive-disagreement-sets-are-self-similar: that claim describes the shape of the closed set where a pair disagrees; this claim reads the pair's agreement at irrational points as equality of colorings of an F-orbit, recovers the stabilizer as a partition stabilizer, and translates the shape dichotomy into transitivity of the stabilizer on irrational orbits
  thompson-f-two-transitive-actions-satisfy-grid-condition: that claim gives injectivity of the left/right orbit pair at one point; this claim adds surjectivity at the good irrational points of the Cantor case, a product decomposition of the whole set
  thompson-f-two-transitive-dyadic-branching-is-binary: that claim is local at a dyadic point, where germs of stabilizers are nontrivial; this claim uses only irrational points, where they are trivial
  thompson-f-two-transitive-disagreement-sets-are-not-cantor: that claim is one half of the shape dichotomy; this claim proves it is equivalent to the stabilizer being transitive on no irrational orbit
  thompson-f-two-transitive-disagreement-sets-have-no-interior: that claim is the other half of the shape dichotomy; this claim proves it is equivalent to the stabilizer being transitive on some irrational orbit
---

Let `F` act on a set `Ω`, `|Ω| ≥ 3`, transitively on ordered pairs of distinct
points. Fix `ω ∈ Ω` and put `H = F_ω`. Use `G_x`, `D(ω_1,ω_2)` and `D_0` as in
`thompson-f-two-transitive-disagreement-sets-are-self-similar`. For
`y ∈ [0,1]` let `F_y` be the stabilizer of the point `y` under the natural
action on `[0,1]`. Call `y ∈ (0,1)` **good** if `G_y` is transitive on `Ω`,
and **bad** otherwise. An `F`-orbit in `(0,1)` is **irrational** if its
points are irrational.

1. (Stalks at irrational points.) If `y` is irrational, then `F_y = G_y`, and
   `G_y·aH ↦ H·a^{-1}y` is a bijection from the `G_y`-orbits on `Ω` onto the
   `H`-orbits on `F·y`.
2. (Colorings.) Let `O` be an irrational orbit. For `ω_1 = aH` put
   `c_{ω_1}(y) = H·a^{-1}y` for `y ∈ O`. This is well defined, it satisfies
   `c_{gω_1} = c_{ω_1} ∘ g^{-1}`, and `c_{ω_1}(y) = c_{ω_2}(y)` holds iff
   `y ∉ D(ω_1,ω_2)`.
3. (Bad orbits.) For an `F`-orbit `O ⊂ (0,1)` the following are equivalent:
   `O` meets `D_0`; `O` meets every disagreement set of a distinct pair; some
   point of `O` is bad; every point of `O` is bad. There are uncountably many
   bad irrational orbits.
4. (Partition stabilizer.) Let `O` be a bad irrational orbit and let `P_O` be
   the partition of `O` into `H`-orbits. Then `ω_1 ↦ c_{ω_1}` is injective on
   `Ω`, and
   `H = { g ∈ F : gP = P for every part P of P_O }`.
   The partition `P_O` has at least two parts, and every part is dense in
   `(0,1)`.
5. (Dichotomy.) Exactly one of the following holds.
   - (A) `D_0` is a Cantor set. The good points form an `F`-invariant
     comeager subset of `(0,1)`. There is an irrational orbit on which `H` is
     transitive, and `H` is transitive on `F·y` for every good irrational `y`.
   - (B) `D_0` has nonempty interior. Every point of `(0,1)` is bad, and `H`
     is transitive on no irrational orbit.
6. (Product splitting at good points.) Let `y` be a good irrational point. Let
   `A_y` (resp. `B_y`) be the elements of `F` supported in `[0,c]` for some
   dyadic `c < y` (resp. in `[d,1]` for some dyadic `d > y`). Then
   `G_y = A_y × B_y`, the map `ω_1 ↦ (B_y ω_1, A_y ω_1)` is a bijection from
   `Ω` onto `Ω/B_y × Ω/A_y`, `A_y` acts on the first factor and trivially on
   the second, `B_y` acts the other way round, and
   `H ∩ G_y = (H ∩ A_y) × (H ∩ B_y)`.

**What this changes.** Given the self-similar claim, item 5 turns the two
open halves of `thompson-f-no-two-transitive-via-disagreement-set-type` into
statements about one subgroup acting on countable dense sets:

- `thompson-f-two-transitive-disagreement-sets-are-not-cantor` is equivalent
  to: **no point stabilizer of a 2-transitive action is transitive on an
  irrational `F`-orbit**;
- `thompson-f-two-transitive-disagreement-sets-have-no-interior` is equivalent
  to: **every point stabilizer of a 2-transitive action is transitive on some
  irrational `F`-orbit**.

Item 4 answers the form question behind the candidate list. Le Boudec–Matte
Bon (arXiv:1906.05744) ask whether stabilizers of partitions of an `F`-orbit
give 2-transitive actions. By item 4 every point stabilizer of a
2-transitive action, if one exists, is of this form, with an irrational
orbit and parts fixed one by one. So Problem 2.20 has a positive answer iff
some partition of some irrational `F`-orbit into at least two dense parts has
a part-wise stabilizer `S` of index at least 3 with exactly two
`(S,S)`-double cosets. Stabilizers
of subsets or partitions of the dyadic orbit, such as Jones' subgroup, can
occur only if they also have this form on an irrational orbit.

Scope: proved here on 2026-09-18 by swarm agent `swarm-0917-w8-w8-z-follow`.
The proof is elementary. There is no independent review, and no novelty is
claimed.

**Proof:** `thompson-f-two-transitive-irrational-orbit-colorings-proof`.
