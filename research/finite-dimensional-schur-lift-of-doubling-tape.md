---
rg: 2
id: finite-dimensional-schur-lift-of-doubling-tape
kind: claim
title: Lift the existing BCS projection-doubling tape through fixed Schur packets in matrix microstates
distinct_from:
  fixed-scale-contextual-multiplicity-holonomy: that asks for a new recurrent network for a generic non-CE BCS; this reuses the explicit shift and polynomial-cost doubling recurrence already present in the self-referential BCS.
  uniform-halting-pauli-word-oracle: that must activate an unbounded verifier size after a halt; every predicate packet here is fixed once and for all.
  trace-functorial-bcs-signal-groupification-impossible: that rules out an exact decoder on all traces; this explicitly asks for a matrix-only multiplicity lift.
---

Construct a finitely presented group `Gamma`, a nonidentity marked word `w`,
and, from every finite-dimensional tuple `V` with total squared normalized-HS
relator energy `E(V)`, nonnegative numbers `a_n(V)<=1` such that for fixed
computable constants `c,K>0`, integer `k`, and every `n>=0`,

```text
a_0(V) >= c ||w(V)-I||_2^2-K sqrt(E(V)),                          (SDL1)

a_n(V) <= (1/2) a_(n+1)(V)+K(n+1)^k sqrt(E(V)).                  (SDL2)
```

The construction must use only the finitely many Schur--Clifford packets for
the fixed contexts of `B_*`. The tape shift `U` supplies all levels by
conjugation; the polynomial factor in `(SDL2)` is allowed because it is
summable against `2^(-n)`.

## Required local interface

1. `boolean-predicate-is-one-rank-jump` compiles each fixed BCS predicate.
2. `finite-schur-clifford-packet-flexible-hs-exactification` turns a small
   local word-table defect into nearby exact packet multiplicities.
3. The exactified multiplicity belonging to the projection
   `P_tilde_n` defines `a_n` at one fixed baseline packet scale.
4. The context-dependent correcting isometries must be compared along the
   actual conjugate tape words so that a violating rank jump pays the
   difference between `a_n` and `a_(n+1)/2`.

Clause 4 is the remaining obstruction. It must be proved by integral/rank
information specific to matrices; a trace-functorial comparison would violate
`trace-functorial-bcs-signal-groupification-impossible`.

## Attempts

- **Independent packet exactification.** Exactifying each context separately
  proves the correct local rank jump, but the Gowers--Hatami correcting
  isometry depends on the context. There is then no common multiplicity vector
  on which the tape conjugation can compare consecutive levels. The attack
  must exactify the overlap algebra or prove that the two corrections agree on
  the marked baseline packet up to `O(sqrt(E))`.
- **Exact trace-functorial overlap.** Forcing one common exact packet atlas in
  every tracial representation is impossible by
  `trace-functorial-bcs-signal-groupification-impossible`. The comparison has
  to use integer multiplicities of finite matrices after local rounding, not a
  universal conditional expectation in the group von Neumann algebra.
- **Deferred calculation.** Write the two context corrections as partial
  isometries over the common selector algebra and estimate their mismatch by
  the polar defect of the overlap intertwiner. A dimension-free estimate here
  would discharge clause 4 and `(SDL2)`.
