---
rg: 2
id: wall-orientation-ambients-need-locally-short-walls
kind: claim
title: A wall-orientation subshift is D-rigid only if every wall's vertex carrier is 2D-connected; over graphical small cancellation groups whose walls pass through relators of unbounded size, as in the Arzhantseva–Osajda and Osajda non-exact groups, the wall ambient is not rigid at any scale, provided walls are quasi-isometrically embedded
requires:
  - ra-counterexamples-are-minimal-sets-of-rigid-ambients
  - rigid-subshifts-over-free-factors-are-tight-almost-everywhere
distinct_from:
  wall-orientation-subshifts-are-quantum-rigid: that is bh-star-b's open claim and proposes wall ambients as (RA′) counterexamples; this proves the carrier condition that any such ambient must meet, and shows that the non-exact small cancellation groups fail it for the whole ambient.
  ra-counterexamples-are-minimal-sets-of-rigid-ambients: that reduces ¬(RA) to minimal sets of rigid ambients; this tests the wall ambient, the leading non-permutational candidate.
---

**ESTABLISHED** for items 1 and 2. **CONDITIONAL** for item 3, on hypothesis (QI) below, which I did
not check against Arzhantseva–Osajda at source. Lane bh-ra-counter, 2026-09-18; not reviewed; no
priority claimed.

## Setting

- `Λ` is finitely generated, with Cayley graph `Cay` for a finite generating set, and a Λ-invariant
  wall structure: every edge lies in exactly one wall, and each wall separates `Cay` into two
  halfspaces.
- The *wall ambient* `X_W ⊆ A^Λ` records at each vertex `λ` which side of each wall dual to an edge at
  `λ` an ultrafilter chooses. This is the Roller compactification coded over `Λ`, and it is a
  subshift.
- The *vertex carrier* `V(w)` of a wall `w` is the set of endpoints of edges of `w`.

## Theorem

1. **Carrier condition.** If some wall `w` has `V(w) = P ⊔ Q` with `P, Q` nonempty and
   `d(P, Q) > 2D`, then `X_W` is not `D`-quantum rigid over any field.
2. **Trees and products pass.** For trees and for `Z²` with its two families of parallel walls, every
   `V(w)` is 1-connected. This is consistent with bh-star-b's rigidity of those ambients.
3. **Non-exact small cancellation groups fail.** Let `Λ` be given by a graphical C′(1/6) presentation
   with walls whose relator graphs have unbounded girth. By Gromov's and Osajda's theorems this is
   exactly what non-exactness forces, since finite such presentations give hyperbolic, hence exact,
   groups. Assume:

   **(QI)** each wall, viewed as the hypertree of relators it crosses, is quasi-isometrically embedded
   in `Cay` with uniform constants.

   Then for every `D` some wall satisfies item 1, so `X_W` is not quantum rigid at any scale.

## Proof

1. Let `e ∈ w` join `v` to `v′`. The principal ultrafilters `x_v` and `x_(v′)` lie in `X_W` and differ
   on exactly the wall `w`. So their codings differ at `λ` iff some edge at `λ` lies in `w`, that is,
   `Δ(x_v, x_(v′)) = V(w)`. Lemma 1′ of `rigid-subshifts-over-free-factors-are-tight-almost-everywhere`
   (the two-piece certificate needs only genuine points, or locally legal colourings) then kills
   `D`-rigidity.
2. In a tree a wall is one edge, so `V(w)` has two adjacent vertices. In `Z²` a wall's edges form a
   ladder whose vertices lie on two adjacent lines.
3. Take a relator copy `Θ` of girth `g > 8K(2D + C)` crossed by a wall `w` at two edges `e₁, e₂`. In
   C′(1/6), relators embed isometrically, and a wall cuts a relator cycle in two edges at distance
   `≥ g/2 − O(1)` in `Θ`. The hypertree of `w` splits at `Θ` into the two sides `P ∋ e₁` and `Q ∋ e₂`.
   Any hypertree path from `P` to `Q` crosses `Θ`, so it has length `≥ g/2 − O(1)`. By (QI),
   `d_(Cay)(P, Q) ≥ (g/2)/K − C > 2D`. Apply item 1. ∎

## What this does and does not say about (RA′)

- It kills the whole ambient `X_W`. It does **not** kill minimal subsets of the boundary part, because
  rigidity passes to subshifts but non-rigidity does not.
- A minimal `Y ⊆ ∂X_W` escapes the certificate only if no two locally-`Y`-legal colourings differ
  on a single wall through a large relator.
- The same mechanism should apply to boundary points with an extremal halfspace dual to such a wall.
  That is expected but not proved.
- So the wall route to ¬(RA′) needs walls that are *locally short*: every wall's carrier is
  `2D`-connected for one fixed `D`.
- Graphical small cancellation cannot give that in its non-exact regime. The large relators that embed
  expanders, and so destroy property A, are the same relators that make one wall's carrier split far
  apart.

## Lesson for general BH

**Wall identity must be a local datum for rigidity.**
- In a rigid ambient, a single flip has to be locally recognizable as one flip.
- Non-exactness by expanders is built from relators of unbounded size. That makes the *same wall*
  relation non-local, and the natural Haagerup (wall) ambient falls apart at every scale.

This is one more instance of the pattern behind (RA): the features that make a group non-exact are
exactly features no bounded-radius rule system can see.

A counterexample would have to combine two things:
- a non-exact group whose non-exactness is *not* visible as unbounded local non-recognizability;
- a rigid ambient with locally short "flip witnesses".

Credits: Gromov (random groups and expanders); Arzhantseva–Delzant; Osajda (small cancellation
labellings, residually finite non-exact groups); Arzhantseva–Osajda (Haagerup non-exact groups via
graphical small cancellation with walls); Wise (walls in small cancellation). All recalled, not re-read.
