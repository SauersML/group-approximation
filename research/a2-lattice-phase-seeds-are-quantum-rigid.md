---
rg: 2
id: a2-lattice-phase-seeds-are-quantum-rigid
kind: claim
title: For a lattice acting simply transitively on the vertices of a thick Ã2 building, the phase seed Y_Γ^(N) is D-quantum rigid over every field for all large D, for suitable N
requires:
  - a2-lattices-carry-finite-type-seeds
distinct_from:
  a2-lattices-carry-finite-type-seeds: that proves the seed axioms and that seed idempotents are classical; this is the open rigidity statement for the seed.
  euclidean-building-boundary-shifts-are-quantum-rigid: that asks rigidity of X_Ω; rigidity of the phase-free seed would imply it, which is why this claim uses the phase seed, whose chamber stratum contains the rigid skew product P instead.
  a2-lattice-boundary-skew-shifts-are-quantum-rigid: that is rigidity of the chamber stratum P, obtained from a finitely presented host; this asks for the whole seed, including the wall strata and the seed orbit.
---

**OPEN** (stated by bh-emitter-b, 2026-09-18). This is rung 1d of the SYNTHESIS v6 gate (SEED).
Notation is that of `a2-lattices-carry-finite-type-seeds`.

**Claim.** There are `N >= 1` and `D_0` such that `Y_Γ^(N)` is `D`-quantum rigid over every field,
for every `D >= D_0`.

**Consequence.** `Γ` then lies in the class `𝒞` of groups with a rigid seed. By
`tree-gluing-turns-rigid-sft-compactifications-into-rigid-sfts`, `Γ * Z` then carries a minimal,
topologically free, quantum-rigid SFT. That is (★′) with a one-ended Kazhdan vertex group, the test
case that matters for Kazhdan inputs.

## What is known

1. **The seed orbit is classical.** In every quantum family, the seed idempotents `S_e` are pairwise
   orthogonal and commute with every letter (`a2-lattices-carry-finite-type-seeds`, item 3). So on
   `W_s = Σ_e S_e W_0` every letter acts by `0` or `1`. A commutator `[E, F]` vanishes as soon as it
   maps `W_0` into `W_s`.
2. **The chamber stratum.** For the `N` of `a2-lattice-boundary-skew-shifts-are-quantum-rigid`, the
   chamber stratum of `∂Y_Γ^(N)` contains a phase coding of `Ω × (Z/N)²` whose minimal pieces are
   phase translates of the rigid `P` (lag conventions not re-checked).
3. **Exact reduction.** The seeds are locally forced, so the claim is equivalent to rigidity of the
   seedless boundary `∂Y_Γ^(N)`. That boundary has no isolated points, so Cantor–Bendixson stops
   there (`a2-seed-rigidity-reduces-to-its-perfect-boundary`).
4. **Necessity of the phase.** Without the phase, rigidity of `Y_Γ` would imply the open
   `euclidean-building-boundary-shifts-are-quantum-rigid`, because `X_Ω ⊆ Y_Γ` and subshifts inherit
   rigidity.

## What remains

1. **The wall strata.** Near a vertex `ξ` at infinity, a seedless field keeps one coordinate finite.
   That coordinate should be a distance in the panel tree of `ξ`, and the field is then a seed of that
   tree times a Busemann direction. The tree argument of `free-group-boundary-shift-is-quantum-rigid`
   (monotone chains, transitivity of `≤`) is the natural tool. None of this is proved.
2. **Gluing.** The strata are not clopen (a description, not proved): the chamber stratum is a closed subshift inside the closure
   of each wall stratum, which is inside the closure of the seed orbit. A proof must pass from each
   stratum to the next.
   - The step from the seed orbit to `∂Y` works once every `D`-pattern that occurs in `Y` but not in
     `∂Y` has product `≤ Σ_(s ∈ F) S_s`, for a finite `F`.
   - Refine the labels by `min(m, K)` and `min(n, K)`; this is still a seed, by the same proof. A letter
     whose two coordinates are both below `K` is then a sum of seed idempotents: descend along its
     exactly known coordinates, using Q3 on each edge and centrality of the `S_e` (lane sketch). This
     gives the needed domination for every pattern that contains such a letter.
   - Patterns with two walls of opposite types need a separate argument. They force an origin within
     a bounded distance, but no single-letter chain reaches it.
3. **A shortcut.** A finitely presented host for `G_V × (Γ ⋉ Y_Γ^(N))` would certify rigidity, through
   `topologically-free-subshift-full-groups-force-quantum-rigidity` (whose freeness hypothesis is only
   topological). Its groupoid is an extension of the boundary groupoid by the pair groupoid of the
   seed orbit.

## Lesson for general BH

Once seeds exist over Kazhdan lattices, rung 1d is a statement about the stratified boundary. The seed
orbit is always classical, and the chamber stratum is already rigid (with the phase). All that is left
is the rank-one wall strata, where tree methods apply, and their gluing.
