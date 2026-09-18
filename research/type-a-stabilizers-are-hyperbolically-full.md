---
rg: 2
id: type-a-stabilizers-are-hyperbolically-full
kind: claim
title: In any action with finitely many orbits on pairs, a point stabilizer with infinite orbit is never elliptic, and never has a quasiconvex orbit with non-full limit set, in any non-elementary action on a hyperbolic space; so locally quasiconvex hyperbolic groups have no type (A) actions, Higman envelopes have none induced from their vertex groups, and the permutational route for a non-exact input needs a hyperbolically full stabilizer
requires:
  - type-a-action-gives-boone-higman-for-subgroups
  - amalgams-of-orbit-finite-actions-are-type-a2
  - ra-counterexamples-are-minimal-sets-of-rigid-ambients
  - fp-simple-nonexact-group
distinct_from:
  ra-counterexamples-are-minimal-sets-of-rigid-ambients: that shows (RA) says nothing against the permutational route; this finds the geometric constraint that route does face, which comes from double cosets, not from exactness.
  amalgams-of-orbit-finite-actions-are-type-a2: that builds type [A_2] actions of amalgams, whose point stabilizers are fundamental groups of finite graphs of groups; this shows such stabilizers are forced to be non-elliptic, so the gluing lemma is consistent with, and in a sense the only shape allowed by, hyperbolic geometry.
  pbh-class-closed-under-graph-products: that is a closure property of B_A; this is a restriction on the actors B_A is built from.
---

**ESTABLISHED** for items 1–3 (lane bh-ra-counter, 2026-09-18; elementary hyperbolic geometry; not
reviewed; very likely folklore, so no priority is claimed). Item 4 is **CONDITIONAL** on the recalled
imports named there.

## Setting

A group `G` acts by isometries on a geodesic hyperbolic space `X`, and the action is
**non-elementary** (two independent loxodromics). `Λ(G) ⊆ ∂X` is its limit set. For `H ≤ G` and
`x ∈ X`, `Λ(H)` is the limit set of the orbit `Hx`.

## Theorem

1. **Double-coset lemma.** Suppose `Hx` is quasiconvex and `Λ(G) ⊄ Λ(H)`. Then `H\G/H` is infinite.
   This covers every `H` with a bounded orbit (elliptic `H`, where `Λ(H) = ∅`).
2. **Type (A) stabilizers are hyperbolically full.** Suppose `G` acts on a set `S` with finitely many
   orbits on two-element subsets (condition 4 of type (A)). Then for every `s` whose orbit is infinite,
   `G_s` is *not* elliptic, and has *no* quasiconvex orbit with `Λ(G) ⊄ Λ(G_s)`, in *any*
   non-elementary action of `G` on a hyperbolic space.
3. **Corollaries.**
   - (a) A non-elementary hyperbolic group has no type (A) action with quasiconvex point stabilizers.
     A locally quasiconvex one has **no** type (A) action at all. This covers free groups, surface
     groups, and many small cancellation and 3-manifold groups.
   - (b) Let `P` split as an amalgam or HNN extension whose Bass–Serre action is non-elementary, for
     example a Higman–Clapham envelope `HNN_s(K × G)` (`higman-clapham-envelopes-are-hnn-over-machine-times-input`).
     No type (A) action of `P` has a point stabilizer inside a conjugate of a vertex group. In
     particular no type (A) action of `P` is induced from an action of a vertex group.
   - (c) The amalgams of `amalgams-of-orbit-finite-actions-are-type-a2` pass this test: their point
     stabilizers are fundamental groups of finite graphs of groups and act on the Bass–Serre tree
     without a fixed vertex.
4. **What this means for a non-exact input.** Let `O` be a finitely generated non-exact group with
   solvable word problem (`decidable-residually-finite-non-exact-group-exists`).
   - **Payoff.** If `O` lies in an fp group `Λ` with a type (A) action, then the twisted
     Brin–Thompson group `SV_Λ` is a finitely presented simple non-exact group. This answers
     `fp-simple-nonexact-group` yes, and makes the exactness separator's (S1) false. That follows from
     Zaremsky's Corollary B, as recorded in `type-a-action-gives-boone-higman-for-subgroups`, since
     exactness passes to subgroups.
   - **Orbit-finiteness is free for `O` itself** (conditional). Suppose `O` is a graphical Gr′(1/6)
     group over a free group with trivial finite radical. Then `O` is acylindrically hyperbolic
     (Gruber–Sisto, recalled). Hence `O` has a faithful highly transitive action (Hull–Osin, recalled),
     so conditions 1 and 4 hold.
   - **What fails.** Condition 2 fails: `O` is infinitely presented, and any finite C′(1/6) presentation
     gives a hyperbolic, hence exact, group. By item 2 applied to the acylindrical action, condition 3
     can only hold with stabilizers whose orbits are not quasiconvex or have full limit set.
   - **So the actor must be an fp overgroup `Λ`** with a hyperbolically full, finitely generated
     stabilizer. By 3(b), it cannot be obtained by inducing `O`'s action up a Higman envelope.

## Proof

1. **A loxodromic avoiding `Λ(H)`.** `Λ(H)` is closed. For a non-elementary action, pairs of fixed
   points of loxodromics are dense in `Λ(G) × Λ(G)` (standard, recalled). So some loxodromic `g` has
   `g^±` in the open set `Λ(G) \ Λ(H)`.

   **Bounded projection.** Let `ℓ` be a quasi-axis of `g`. The nearest-point projection of `Hx` to
   `ℓ` is bounded.
   - If not, there are `h_k x` whose projections run out toward, say, `g^+`.
   - Geodesics `[x, h_k x]` then pass within a uniform distance of `ℓ(t_k)`, with `t_k → ∞`, by thin
     quadrilaterals.
   - By quasiconvexity these points lie near `Hx`, which forces `g^+ ∈ Λ(H)`. Contradiction.

   **Separation.** The projection of `g^n Hx = g^n(Hx)` lies near `g^n·(bounded) ⊆ ℓ` at distance
   about `nτ` along `ℓ`, where `τ > 0` is the translation length. In a hyperbolic space two sets whose
   projections to a quasi-geodesic are far apart are at least that far apart, up to a constant. So
   `d(Hx, g^n Hx) ≥ nτ − C`.

   **Counting.** For `h, h′ ∈ H`, `d(x, h g^n h′ x) = d(h^(-1)x, g^n h′ x) ≥ d(Hx, g^n Hx)`. So the
   function `HkH ↦ min_(k′ ∈ HkH) d(x, k′x)` is unbounded on `{H g^n H}`, and infinitely many of these
   double cosets are distinct. ∎
2. Let `O_s = Gs` be infinite. Orbits of `G` on two-element subsets of `O_s` correspond to the
   non-trivial double cosets `G_s k G_s` modulo inversion. So `G_s\G/G_s` is finite, and item 1 forbids
   the listed shapes of `G_s`. ∎
3. (a) Apply item 2 with `X` a Cayley graph. A quasiconvex infinite-index subgroup has
   `Λ(H) ≠ ∂G` (standard, recalled). A finite-index stabilizer gives a finite orbit. If every orbit is
   finite, `S` is a union of finitely many finite orbits (by condition 4), and an infinite group cannot
   act faithfully on a finite set. (b) Vertex groups are elliptic on the Bass–Serre tree. Induced
   actions have stabilizers inside conjugates of the inducing subgroup. (c) This is the graph-of-groups
   description in the gluing lemma's proof. ∎
4. As stated. ∎

## Calibration

- `V` on the dyadic points is a type (A) actor. `V` has no non-elementary action on a hyperbolic space
  with the forbidden stabilizers: dyadic stabilizers of `V` are not elliptic in any such action. This
  is consistent, and item 2 gives no obstruction.
- Free groups are highly transitive (Dixon, McDonough; recalled), with infinitely generated
  stabilizers. That is consistent with 3(a).

## Lesson for general BH

**The permutational route is blocked neither analytically nor by (RA). It is constrained
geometrically, by double cosets.**
- A type (A) point stabilizer must be *hyperbolically full*: never elliptic and never "small at
  infinity" in any non-elementary hyperbolic action.
- So a Higman-style overgroup of an input cannot carry a type (A) action pulled up from its vertex
  groups. The stabilizer has to spread across the whole splitting, which is exactly the shape of the
  gluing lemma's graph-of-groups stabilizers.
- For Osajda's input, orbit-finiteness comes for free (Hull–Osin, conditionally). The whole difficulty
  is one finitely generated, hyperbolically full stabilizer in a finitely presented overgroup, plus
  kernel removal if the action is built by gluing.
- One success would give the first finitely presented simple non-exact group.

Credits:
- highly transitive actions of acylindrically hyperbolic groups: Hull–Osin;
- acylindrical hyperbolicity of graphical small cancellation groups: Gruber–Sisto;
- non-exact groups: Gromov, Arzhantseva–Delzant, Osajda;
- property A and exactness: Higson–Roe, Ozawa;
- finite presentation of twisted Brin–Thompson groups: Zaremsky;
- type (A), [A_2] and relative PBH: BFFHZ, FFWZ;
- double-coset and width phenomena for quasiconvex subgroups: Gitik–Mitra–Rips–Sageev.

All are recalled, not re-read at source.
