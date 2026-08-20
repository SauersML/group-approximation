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

`finite-group-shared-overlap-polar-alignment` now supplies the pairwise
comparison on a submodule of dimension `d-O(eta^2d)`. The remaining part of
clause 4 is to choose these large intertwiners compatibly around the tape
cycle and show that their discarded corners have the polynomially weighted
cost in `(SDL2)`. It must be proved by integral/rank information specific to
matrices; a trace-functorial comparison would violate
`trace-functorial-bcs-signal-groupification-impossible`.

## Attempts

- **Independent packet exactification. Pairwise part repaired.** Exactifying
  each context separately gives different correcting isometries.
  `finite-group-shared-overlap-polar-alignment` averages their overlap and
  produces an exact common-subgroup intertwiner after discarding only
  `O(eta^2d)` dimensions. What is not yet proved is simultaneous choice of
  these polar intertwiners along all tape incidences without accumulating an
  unsummable holonomy loss.
- **Exact trace-functorial overlap.** Forcing one common exact packet atlas in
  every tracial representation is impossible by
  `trace-functorial-bcs-signal-groupification-impossible`. The comparison has
  to use integer multiplicities of finite matrices after local rounding, not a
  universal conditional expectation in the group von Neumann algebra.
- **Next calculation.** Compose the pairwise polar intertwiners around one
  recurrence cell. Its failure to close lies in the commutant of the baseline
  packet. Bound the rank of the nontrivial polar holonomy by the original
  shared-word defect, or absorb it into the next tape level with factor
  `1/2`. This is the remaining route to `(SDL2)`.
