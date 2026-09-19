---
rg: 2
id: a2-phase-seed-passes-the-separability-test
kind: claim
title: Every modification of a point of the Ã2 phase seed changes it on a tail toward that point's own limit (the origin, deep subsectors toward its chamber, or ray tails toward its wall vertex), and such tails always meet; so the Ã2 phase seed has no separable modifications, and the opposite-type wall patterns are harmless for this test
distinct_from:
  rigid-seed-constructions-pass-the-separability-test: that audits the building seeds only in apartments and flags the wall strata; this settles the Ã2 seed in the whole building.
  a2-lattice-phase-seeds-are-quantum-rigid: that is the open quantum rigidity of the seed; this proves the classical necessary condition, so no classical freedom stands in its way.
---

**ESTABLISHED** (lane bh-free-09, 2026-09-18; elementary lane proof, not independently reviewed; no
priority claimed). It uses three standard facts about Euclidean buildings, recalled and not
re-derived:
- (B1) any sector and any chamber at infinity have a subsector in a common apartment;
- (B2) along a geodesic ray `r` toward `ξ`, the Alexandrov angle `∠_(r(t))(ξ, η)` increases to the Tits
  angle `∠(ξ, η)`;
- (B3) in the spherical building of an `Ã₂` building (a projective plane), two distinct vertices of
  one type are at Tits angle `120°`.

## Setting

As in `a2-lattices-carry-finite-type-seeds`. The label `a_o(x)` is the simplex of `Lk(x)` containing
the germ of `[x, o]`; the phase version adds `σ(o, x) mod N`. The points of `Y_Γ^(N)` are of three
kinds:
- **seed-orbit points**, the fields `y_o`;
- **chamber points**, toward a chamber `c` at infinity: the label at `x` is the chamber of `Lk(x)`
  containing the germ of the sector `Q(x, c)`;
- **wall points**, toward a vertex `ξ` at infinity with a ray class `ω`: the label is the wall germ
  of `ξ` on the tree `W_ω` of rays toward `ξ` in class `ω`, and a flag adjacent to `ξ` elsewhere;

each with a phase. That these exhaust the boundary is the stratification recorded on the `Ã₂` nodes.

## Theorem

Call a *tail toward* a point's limit:
- for `y_o`, the vertex `o`;
- for a chamber point, the deep part of any sector toward `c`;
- for a wall point, a tail of any ray of `W_ω`.

1. **Every modification changes the point on a tail toward its own limit.**
2. **Tails toward one limit meet.** Two sectors toward `c` share a subsector, and two rays of `W_ω` are
   strongly asymptotic, so they share a tail.

Hence any two modifications of one point have intersecting difference sets. **`Y_Γ^(N)` passes the
separability test at every scale.**

## Proof of item 1

- **Seed-orbit points.** If `y ≠ y_o`, then `y(o) ≠ *`, since `*` at `o` forces `y_o`.
- **Phase-only changes.** They change the phase at every vertex.
- **Wall point `(ξ, ω)`.** Let `y'` be a modification.
  - *`y'` is a chamber point, or a wall point with a vertex of the other type, or a wall point toward
    `ξ` with a class `ω' ≠ ω`.* At `x ∈ W_ω` the old label is the wall germ of `ξ`. The new label there
    is a flag, a wall germ of the other type, or, since `x`'s ray to `ξ` is not of class `ω'`, a flag.
    So `y'` differs on all of `W_ω`.
  - *`y'` is a wall point toward `ξ' ≠ ξ` of the same type.* By (B3) `∠(ξ, ξ') = 120°`. By (B2),
    far along any ray `r ⊆ W_ω` the germs toward `ξ` and `ξ'` make a positive angle. Angles between
    simplicial germs are discrete, so the germs are different vertices of `Lk(r(t))` for large `t`. So
    `y'` differs on a tail of `r`.
- **Chamber point `c`.** Let `y'` be a modification.
  - *`y'` is a chamber point `c'`.* In every apartment containing `c` and `c'`, the germs toward `c` and
    `c'` differ at every vertex, as in `building-transplants-pass-the-separability-test`, item 1. By
    (B1) every sector toward `c` has a subsector in such an apartment.
  - *`y'` is a wall point `(ξ, ω)`.* Take a sector `S` toward `c` and an apartment `A ⊇ S`.
    - If `ξ` is not a vertex of `c`, the new labels near `ξ` are never the chamber `c` deep in `S`.
    - If `ξ` is a vertex of `c`, then deep in `S` the tree coordinate of `x` in the panel tree of `ξ`
      runs toward the end on `c`'s side, away from `ω`. So the direction to the limit leaves from the
      other side, and the label is the other chamber adjacent to `ξ`. In the apartment model this is
      the half-plane computation: points above the wall line get the chamber below.
    - Either way, `y'` differs on the deep part of `S`. `∎`

## About the opposite-type wall patterns

The `Ã₂` node leaves open the patterns that contain wall labels of both types. They force an origin
within bounded distance (`a2-lattice-phase-seeds-are-quantum-rigid`, What remains 2), so they occur
only in seed-orbit points, whose modifications all change the origin. **They create no separable
freedom.** Their difficulty is quantum: gluing the strata in a quantum family.

## For `C̃₂` (not settled)

The labels of `c2-building-lattices-carry-finite-type-seeds` are graph-distance gradients (inward
sets), not CAT(0) germs, so (B2) does not apply directly. The apartment computation of
`rigid-seed-constructions-pass-the-separability-test` finds the same tail property. A proof needs the
horofunction description of the `C̃₂` graph metric.

## Lesson for general BH

- **In horofunction seeds, a point's freedom always reaches its own limit.** Any change of a boundary
  field alters it arbitrarily far toward the place it came from. Such changes can never be pulled
  apart.
- **The classical side of the `Ã₂` seed is clean.** What remains for its rigidity is purely quantum:
  gluing the seed orbit, the wall strata and the chamber stratum inside one family. That is where the
  `Ã₂` lane should put its effort.
