---
rg: 2
id: a2-phase-seed-passes-the-separability-test
kind: claim
title: Every modification of a point of the Ã2 phase seed changes it on a tail toward that point's own limit (the origin, deep subsectors toward its chamber, or ray tails toward its wall vertex), and such tails always meet; so the Ã2 phase seed has no separable modifications, and the opposite-type wall patterns are harmless for this test
distinct_from:
  rigid-seed-constructions-pass-the-separability-test: that audits the building seeds only in apartments and flags the wall strata; this settles the Ã2 seed in the whole building.
  a2-lattice-phase-seeds-are-quantum-rigid: that is the open quantum rigidity of the seed; this proves the classical necessary condition, so no classical freedom stands in its way.
---

**ESTABLISHED, conditional on the boundary description (S) below** (lane bh-free-09, 2026-09-18,
revised 2026-09-19; elementary lane proof, not independently reviewed; no priority claimed).

The 09-19 revision closes three gaps of the first version: seed-orbit modifications of boundary
points, the case of a wall vertex off the chamber, and the unstated use of (S). The chamber case of
(S) is now proved here.

## Facts used

These are standard facts about Euclidean buildings, recalled and not re-derived:
- (B1) any sector and any chamber at infinity have a subsector in a common apartment;
- (B2) along a geodesic ray `r` toward `ξ ∈ ∂Δ`, the angle `∠_(r(t))(ξ, η)` increases to the Tits
  angle `∠(ξ, η)`, and `∠_(r(t))(ξ, o) → 180°` for a fixed vertex `o`;
- (B3) distinct vertices of one type of the spherical building (a projective plane) are at Tits angle
  `120°`, and opposition exchanges the two types;
- (B4) angles are upper semicontinuous: if `o_n → η` in the cone topology, the direction of
  `[x, o_n]` at `x` tends to that of `[x, η)`.

## The boundary description (S)

Notation is that of `a2-lattices-carry-finite-type-seeds`. For a vertex `ξ` of `∂Δ`, `T_ξ` is its panel
tree, whose vertices are the classes of eventually coinciding rays toward `ξ`, and `π_ξ(x)` is the class
of the ray from `x`. Up to the phase coordinate, every point of `Y_Γ^(N)` is one of the following.
- A **seed-orbit point** `y_o`.
- A **chamber point** `y_c`: at `x`, the chamber germ of `Q(x, c)`.
- A **wall point** `y_(ξ,p)`, where `p` is a vertex of `T_ξ`:
  - at `x ∈ W_p = π_ξ^(-1)(p)` the label is the `ξ`-germ, a vertex of `Lk(x)`;
  - elsewhere it is the chamber of `Lk(x)` that contains the `ξ`-germ and corresponds to the first
    edge of `[π_ξ(x), p]` in `T_ξ`.

**Proved part.**
- By (S3) every point is a limit of `y_(o_n)`. A bounded sequence `o_n` gives a seed-orbit point.
- Otherwise pass to a subsequence with `o_n → η ∈ ∂Δ`. By (B4), each label contains the simplex
  carrying the direction of `[x, η)`.
- If `η` is regular, lying in the open chamber `c`, that simplex is the chamber germ of `Q(x, c)`, so
  the limit is `y_c`.
- If `η = ξ` is a vertex, every label is the `ξ`-germ or a chamber containing it.

**Not proved here.** That in the vertex case the choice of chamber is a `T_ξ`-pointer toward one vertex
`p`. A limit toward an end of `T_ξ` would give a chamber point. This is the wall-stratum description of
`a2-lattice-phase-seeds-are-quantum-rigid` (What remains, item 1), which is supported there by the
local tables: one inward and `q²` outward wall neighbours, with outward ones forced to point back.

## Theorem (given (S))

1. Let `y` be a point and `y'` a modification of it. Then `y'` differs from `y`:
   - at `o`, if `y = y_o`;
   - on a subsector of every sector toward `c`, if `y = y_c`;
   - on a tail of every ray toward `ξ` contained in `W_p`, if `y = y_(ξ,p)`.
2. Two subsectors of sectors toward `c` meet, and so do two tails of one ray. So any two modifications
   of one point have intersecting difference sets, and `Y_Γ^(N)` passes the separability test
   (`cross-layer-separable-modifications-kill-quantum-rigidity`) at every scale.

## Proof of item 1

- **Phase-only modifications** change the phase at every vertex.
- **`y = y_o`.** If `y'(o) = *`, then `y' = y_o`.
- **`y = y_(ξ,p)`.** Here `y(x)` is the `ξ`-germ on `W_p`. Fix a ray `r ⊆ W_p` toward `ξ`.
  - *`y'` is a chamber point, a wall point whose vertex has the other type, or `y_(ξ,p')` with
    `p' ≠ p`.* On `W_p`, the label `y'(x)` is a chamber, a vertex of the other type, or (since
    `π_ξ(x) = p ≠ p'`) a chamber. So `y'` differs on all of `W_p`.
  - *`y' = y_(ξ',p')` with `ξ' ≠ ξ` of the same type.* `y'(r(t))` contains the `ξ'`-germ. By (B2) and
    (B3), `∠_(r(t))(ξ, ξ') > 0` for large `t`. Angles between vertex germs are discrete, so the
    `ξ`-germ and the `ξ'`-germ are different vertices. So `y'(r(t))` is not the vertex `ξ`-germ.
  - *`y' = y_o`.* `a_o(r(t))` contains the germ toward `o`, which by (B2) makes an angle `> 60°` with the
    `ξ`-germ for large `t`. So `a_o(r(t))` is not the `ξ`-germ.
- **`y = y_c`.** Fix a sector `S` toward `c`.
  - *`y' = y_(c')`.* By (B1), some subsector of `S` lies in an apartment `A` with `c' ∈ ∂A`. At every
    vertex of `A` the sectors toward `c` and toward `c'` are different Weyl cones, so their germs
    differ.
  - *`y' = y_(ξ,p)` with `ξ ∉ c`.* Choose a chamber `c'' ∋ ξ`, and by (B1) a subsector `S' ⊆ S` in an
    apartment `A` with `c'' ⊆ ∂A`. At `x ∈ S'`, `y'(x)` contains the direction of the `ξ`-ray in `A`.
    That direction is not a vertex direction of the Weyl cone `Q(x, c)`, since in a flat, distinct
    points at infinity have distinct directions. So `y'(x) ≠ y(x)`.
  - *`y' = y_(ξ,p)` with `ξ ∈ c`.* In an apartment `A ⊇ S`, the line `T_ξ ∩ A` has the end `e_c` of
    `c`. Deep in `S`, meaning on a subsector, `π_ξ(x)` lies on the ray from the junction of
    `[p, e_c)` with that line toward `e_c`. There the first step toward `p` points away from `e_c`,
    while `y(x)` points toward `e_c`. On `W_p` the label is a vertex.
  - *`y' = y_o`.* The sectors `Q(o, c)` and `S` share a subsector `S*`. For `x ∈ S*`, the germ of
    `[x, o]` lies in the closed cone opposite to `Q(x, c)`, which shares no simplex with the chamber
    germ of `Q(x, c)`. `∎`

## The opposite-type configuration: settled for this test

**What was open.** The rigid-seed audit flagged one case: a wall point toward `ξ` modified to a point
toward a vertex of the other type. That includes the opposite vertex `ξ̄`, whose wall line shares a
singular line with the old one.

**Answer.** Such a modification changes the point on **all of `W_p`**. On `W_p` the old labels are
vertices of one type, and the new labels are vertices of the other type or chambers. So it creates no
separable freedom.

**Where the opposite-type patterns occur.** Under (S), they occur only in seed-orbit points, and only
within bounded distance of the origin. Boundary points carry vertex labels of at most one type. In
`y_o`, a line label at vector distance `(m, 0)` and a point label at `(0, n)` within distance `R` force
`max(m, n) <= 2R`, because the vector distance is 1-Lipschitz. So their difficulty is purely quantum:
gluing the strata inside one family (`a2-lattice-phase-seeds-are-quantum-rigid`, What remains, item 2).

## For `C̃₂` and `C̃_n` (not settled)

The `C̃_n` seeds (`c2-building-lattices-carry-finite-type-seeds` and bh-invent-13's polar-projection
seeds) use graph-distance or projection labels, not CAT(0) germs, so (B2) and (B4) do not apply
verbatim. The same proof goes through once two facts are known:
- every boundary point is an origin, a chamber pointer or a panel-tree pointer;
- labels of distinct limits separate along rays.

## Lesson for general BH

- **In horofunction seeds, a point's freedom always reaches its own limit.** The origin, deep
  subsectors and ray tails are each such a limit, and changes that reach one limit cannot be pulled
  apart.
- **Type is a free separator.** A modification that changes the type of the vertex at infinity
  changes every vertex label at once.
- **For the `Ã₂` seed, the classical side is clean.** Its rigidity reduces to the quantum gluing of the
  three strata, and to one geometric input (S) for the wall strata.
