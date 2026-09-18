---
rg: 2
id: decidable-groups-embed-in-rigid-sft-compactification-groups
kind: claim
title: Every finitely generated group with solvable word problem embeds in a finitely presented group that has a quantum-rigid SFT compactification (one isolated seed orbit, dense, with trivial stabilizer)
requires:
  - tree-gluing-turns-rigid-sft-compactifications-into-rigid-sfts
  - decidable-host-classes-reduce-to-canonical-kazhdan-groups
distinct_from:
  decidable-groups-lie-in-fp-groups-with-rigid-topfree-sfts: that asks for a rigid minimal topologically free SFT over an overgroup; this asks for a rigid SFT compactification, with no minimality and an isolated orbit, and implies it through free product with Z.
  decidable-groups-embed-in-fp-groups-with-minimal-free-sft: that is P1, which asks for existence of a free minimal SFT with no rigidity; this asks for a deterministic object, a locally checkable coordinate system with a unique origin, that is rigid.
---

**OPEN** (lane bh-g2-buildings, 2026-09-18). This is premise (★𝒞) of route
`rigid-topfree-sfts-via-rigid-sft-compactifications`.

## Statement

For every finitely generated `G` with solvable word problem there is a finitely presented `Λ_0 ≥ G` in
the class `𝒞` of `tree-gluing-turns-rigid-sft-compactifications-into-rigid-sfts`. That is, there are:
- an SFT `Y` over `Λ_0`;
- a seed pattern whose cylinder is a single point `y_*` with trivial stabilizer and dense orbit;
- rigidity: `Y` is `D`-quantum rigid over every field for all large `D`.

## What is known

- **Consequence.** (★𝒞) implies `decidable-groups-lie-in-fp-groups-with-rigid-topfree-sfts` via
  `Λ = Λ_0 * Z` (the route). The overgroup obtained there is `Λ_0 * Z`.
- **Canonical inputs suffice.** By `decidable-host-classes-reduce-to-canonical-kazhdan-groups`, applied
  to the class of finitely presented members of `𝒞`, (★𝒞) is equivalent to the same statement for the
  groups `H_Γ = EL_3(R_Γ)`. These are infinite, finitely generated, simple and Kazhdan.
- **Closure operations do not carry inputs.** `𝒞` contains finite groups and `Z`, and is closed under
  `×` and `*`. But a simple group inside `A × B` embeds in `A` or in `B`, and a group with (FA) inside
  `A * B` lies in a conjugate of `A` or of `B`. So each `H_Γ` must lie in a member of `𝒞` that is not
  obtained from smaller ones by these operations. The groups generated from finite groups and `Z` by
  `×` and `*` have easy word problems, so they can never do it.
- **Geometry is forced into `Y`.** An `H_Γ` acts trivially on every locally finite tree and every
  Bruhat–Tits building (`kazhdan-simple-groups-act-only-on-exotic-2d-buildings`). So no tree or
  Bruhat–Tits factor of `Λ_0` sees the input, and `Y` must code its geometry.
- **Decidability is consumed.** A finitely presented member of `𝒞` has solvable word problem. This
  comes from the minimal topologically free rigid SFT on `Λ_0 * Z` and
  `rigid-topologically-free-sfts-force-solvable-word-problem`.
- **Finite-state codings are not enough.** Any `Y` whose seed-forced configuration `y_*` is produced by
  a finite-state cone-type rule inherits the word-problem cap of
  `finite-state-li-coded-full-groups-have-exponential-word-problem` in spirit. Tree and building
  pointer codings are of this kind. (This is a heuristic, not a theorem here.)

## Test cases (all open here)

- **Hyperbolic groups.** Do gradient fields of distance-to-a-point functions, with Cannon's finitely
  many cone types as local rules, give a rigid SFT compactification? The difficulty is that "one sink" must
  be locally checkable.
- **Cocompact Ã₂ lattices.** Is there a sector-coordinate compactification, combining a pointer to a
  vertex with the Weyl-chamber direction?
- **Z², BS(1,2), Heisenberg.** For `Z²` the answer is yes: the product of two copies of `C_Z`. For
  `BS(1,2)` and `H_3(Z)` it is unknown. In `H_3`, the central coordinate relative to the seed changes by
  unbounded amounts along generators, so sign fields alone do not work.
- **A hard-WP member.** Find an `fp` group with word problem of arbitrary given degree (for example a
  Clapham-type envelope) in `𝒞`. This is the whole content of (★𝒞).

## Lesson for general BH

The E1′ + E2 gate is a question about coordinate systems. Do finitely presented overgroups of the
canonical Kazhdan inputs admit a locally checkable, quantum-rigid coordinate system with a unique
origin? Minimality, topological freeness and the tree geometry come for free once they do. Any
counterexample mechanism must show that such coordinate systems cap the word problem.
