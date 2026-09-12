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
