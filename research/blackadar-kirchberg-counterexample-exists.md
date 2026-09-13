---
rg: 2
id: blackadar-kirchberg-counterexample-exists
kind: claim
title: Some separable nuclear stably finite C*-algebra is not quasidiagonal (negative answer to STW Problem VII)
root: true
distinct_from:
  stw99-problem-vii-blackadar-kirchberg: that is the positive conjecture; this is its negation, carried as a separate root so that refutation routes have a target.
  stw07-counterexample-has-singular-trace-normal-form: that is the normal form a counterexample must have; this is the existence statement itself.
artifacts:
  - research/artifacts/stw07-k0-hahn-banach-trace-sign-2026-09-11.md
  - research/artifacts/stw07-status-and-stable-character-reduction-2026-08-30.md
---

**OPEN.**  There is a separable nuclear stably finite C\*-algebra that is not
quasidiagonal.

## Attempts

- **Trace-positive K_0-classes.**  Route
  `bk-counterexample-via-qd-trace-positive-class` builds an explicit
  extension `0 -> K tensor A -> E -> C(T) -> 0` from a quasidiagonal nuclear
  `A` with a singular class positive on its quasidiagonal traces.  Its open
  input `qd-nuclear-algebra-with-qd-trace-positive-singular-class` needs a
  failure of the exact X(1) residual and a non-UCT nuclear quotient, per
  `stw07-trace-obstruction-forces-nonqd-trace-and-non-uct`.
- **Ordered-group obstructions on finite data: none.**  Artifact Lemma 3:
  singularity alone makes every finite window of rank constraints feasible,
  both killing and negating the class.  So a counterexample is not detected
  by `K_0` order data on finite windows.
- **Normal form.**  `stw07-counterexample-has-singular-trace-normal-form`: a
  counterexample may be taken with a character whose stable essential kernel
  carries an unbounded trace and no bounded one.
- **Quotient-detected candidates: dead (2026-09-12).**
  `stw07-separating-qd-quotients-force-quasidiagonality`: any algebra whose
  quasidiagonal quotients separate points is quasidiagonal.  This kills
  C(X)-algebras with quasidiagonal fibres (continuous or not), residually
  finite-dimensional algebras, and algebras residually in the solved classes.
  A counterexample has a nonzero quasidiagonal radical `R_qd(E)`.
- **Compact-free index carriers: dead (2026-09-12).**
  `bk-no-compact-open-ideals-are-qd-invisible`: an extension of a nuclear
  quasidiagonal algebra by an exact ideal with no compact open primitive subset
  is quasidiagonal, with no UCT hypothesis.  So suspension-like, cone-like and
  field-over-a-line ideals cannot carry the index obstruction.
  `stw07-qd-radical-criterion-compact-open`: `E` is quasidiagonal iff
  `Prim(R_qd(E))` has no compact open subset.  A counterexample therefore has a
  compact ideal inside `R_qd(E)` carrying a lower semicontinuous trace with a
  finite nonzero value.
- **Gluing reduction (2026-09-12).**  Problem VII is equivalent to its case
  `A = J_1 + J_2` with both ideals compact-free, hence AF-embeddable (take
  `C([0,1], B)` for a counterexample `B`).  Quasidiagonality on an open cover of
  the primitive spectrum carries no information.  The problem is gluing traced
  compact ideals.
- **Fibrewise shape (2026-09-12).**
  `bk-primitive-quotients-qd-or-traceless-force-qd`: if every primitive
  quotient is quasidiagonal or traceless, the algebra is quasidiagonal.  So a
  counterexample has a nonempty compact open set of non-quasidiagonal primitive
  quotients, at least one of them traced; under the UCT that one is prime but
  not simple.  Continuous fields with simple UCT fibres, including Kirchberg
  fibres, are never counterexamples.  For `T_1` spectra, a counterexample exists
  iff a simple one does (`bk-t1-primitive-spectrum-case`).
- **Trichotomy (2026-09-12).**  `bk-counterexample-trichotomy-via-qd-radical`:
  a counterexample either has no nonzero quasidiagonal quotient, or has a
  radical that is again a counterexample, or is glued from a quasidiagonal
  radical by a nonzero Ext class.  In the last case it refutes the UCT-quotient
  extension conjecture (hence universal K_0-Hahn--Banach), or its quotient is a
  non-UCT nuclear algebra.
