---
rg: 2
id: simultaneous-block-escaping-context-holonomy
kind: claim
title: Couple the one-marginal free-phase cells without disturbing previously identified overlaps
artifacts:
  - research/artifacts/signed-hecke-common-type-normalization-2026-08-20.md
distinct_from:
  signed-hecke-block-escaping-cycle-holonomy: that states the complete balanced projection-atlas construction; this isolates the composition law needed after one binary block-escaping chord has been constructed explicitly.
  fresh-selector-renewal-after-symplectic-chart-reset: that renews approximate Fanizza selector packets with an HS estimate; this asks for exact equality of finitely supported algebraic projections in a signed group corner.
---

Starting from the exact one-edge unitary `(OBM3)`, construct finitely many
coupled free-phase or piecewise-transport cells so that a single unitary
`V_c` for each context satisfies every overlap equation `(BCH2)` incident to
that context.  The construction must retain at least one non-root context
atom and have finite group-word support.

The coupling may enlarge the finite packet and may use higher-dimensional
Hadamard rotations inside rationally balanced fibers.  It must not replace
one context by independently conjugated copies for its different variables:
all of its marginals have to arise from the same atom partition `(BCH1)`.

## Attempts

- **Independent one-edge cells: inconsistent.**  They give a different
  conjugated atom partition for each incident variable, so they do not define
  one context PVM.
- **Sequential conjugation: not triangular.**  A later free-phase unitary
  preserving the new marginal generally moves the marginals fixed at earlier
  steps.  `sequential-marginal-holonomy-is-conditional-rank-matching` gives
  the exact feasibility test: every conditional plus/minus rank must match in
  every joint atom of the already frozen marginals.  Unconditional balance is
  only the first step.
- **Centralize every previous marginal: can freeze the atlas.**  Mixing only
  within their joint eigenspaces preserves them, but if those joint atoms
  coincide with the context assignment atoms then the conjugation leaves the
  entire context diagonal algebra unchanged.
- **Live finite target.**  Find a rotation whose support graph lies inside
  every already-fixed sign fiber but crosses at least one remaining context
  atom, then choose free phases constant exactly on the fixed marginal blocks.
  `free-phase-context-escape-criterion` proves that such a rotation exists
  exactly when the already-fixed marginals do not separate the supported
  assignments.  Whether contexts and chords can be ordered so this condition
  persists, or whether a higher cell can cross the first separating cycle,
  is the concrete finite incidence/linear-algebra question.
- **Join-tree composition is solved.**
  `join-tree-bcs-has-explicit-signed-hecke-atlas` adjoins fresh direct-product
  free phases at each child and uses full-overlap rational balancing.  The
  running-intersection property makes the construction triangular.  Hence
  only non-tree chords remain; `signed-hecke-cycle-only-route` isolates the
  first one as `first-cycle-signed-hecke-chord`.
- **Every finite family of escape cells on one context is now classified for
  fixed targets.** `finite-chord-context-is-joint-table-plus-collision` shows
  that the proposed target signs must commute and that their complete joint
  rank table must match inside every previously frozen fiber.  Matching the
  one-sign tables separately is insufficient.  When the joint table matches,
  one common context unitary installs all signs; a finite-support free-phase
  escape exists exactly when the enlarged frozen tuple still has two distinct
  assignments in one joint fiber.  The local higher-valence problem therefore
  collapses to a finite joint table.  What remains is global: choose compatible
  target tuples around every cycle, or escape a collision-free context by a
  non-conjugation additive operation.
- **The global target problem is a fixed-profile boundary BCS.**
  `global-chord-target-selection-is-fixed-profile-boundary-bcs` writes the
  exact matrix equations.  Only its globally commuting sector is an integer
  multi-marginal transport polytope.  Balanced one-variable ranks do not
  imply feasibility: an unconstrained three-context triangle can prescribe
  equality, equality, and inequality joint tables with balanced single-site
  ranks, forcing `Z_1=Z_2=Z_3=-Z_1`.  If every context variable is shared,
  global target selection is already an exact finite-dimensional model of
  the original BCS and is impossible for the no-CE source.  Free-phase
  collisions help only in private extension fibers after the boundary model
  exists.
