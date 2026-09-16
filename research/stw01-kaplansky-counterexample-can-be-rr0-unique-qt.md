---
rg: 2
id: stw01-kaplansky-counterexample-can-be-rr0-unique-qt
kind: claim
title: A Kaplansky counterexample can be RR0 with a unique quasitrace
distinct_from:
  stw01-traceless-separable-simple-reduction: that gives a traceless separable simple stably finite witness carrying some nonadditive quasitrace; this makes the normalized 2-quasitrace unique and adds real rank zero, stable rank one, a unital CAR subalgebra and comparison of projections by the quasitrace.
  stw01-separable-simple-reduction: that only cuts a nonadditive AW*-factor quasitrace down to a separable simple stably finite algebra, with no control of the quasitrace space, real rank or stable rank.
artifacts:
  - research/artifacts/stw01-rr0-witness-faithful-state-frontier-2026-09-16.md
---

If STW Problem I has a negative answer, then there is a separable, unital,
simple, non-elementary, stably finite C*-algebra `A` such that:

1. `A` has real rank zero and stable rank one;
2. `A` contains a unital copy of the CAR algebra `M_{2^infty}`;
3. `A` has **exactly one** normalized 2-quasitrace `q_A`, and `q_A` is faithful and
   not additive;
4. `A` has no tracial state and is not exact;
5. for projections `e,f` in `A`, `q_A(e) < q_A(f)` implies `e <~ f` in `A`.

Consequently STW Problem I is equivalent to the following assertion: every
separable unital simple C*-algebra of real rank zero and stable rank one with a
unique normalized 2-quasitrace has a tracial state. The converse direction is
immediate, because a tracial state is a normalized 2-quasitrace.

This is a normal form for counterexamples, not progress on either side of the
problem.
