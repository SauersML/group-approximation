---
rg: 2
id: finite-dimensional-schur-lift-of-doubling-tape
kind: claim
title: Lift the existing BCS projection-doubling tape through self-similar Schur cells in matrix microstates
distinct_from:
  fixed-scale-contextual-multiplicity-holonomy: that asks for a new recurrent network for a generic non-CE BCS; this reuses the explicit shift and polynomial-cost doubling recurrence already present in the self-referential BCS.
  uniform-halting-pauli-word-oracle: that must activate an unbounded verifier size after a halt; every predicate packet here is fixed once and for all.
  trace-functorial-bcs-signal-groupification-impossible: that rules out an exact decoder on all traces; this explicitly asks for a matrix-only multiplicity lift.
---

Construct a finitely presented group `Gamma`, a nonidentity marked word `w`,
and, from every finite-dimensional tuple `V` with total squared normalized-HS
relator energy `E(V)`, nonnegative numbers `a_n(V)<=1` such that for fixed
computable constants `c,K>0`, integer `k`, one `0<lambda<1`, and every `n>=0`,

```text
a_0(V) >= c ||w(V)-I||_2^2-K sqrt(E(V)),                          (SDL1)

a_n(V) <= lambda a_(n+1)(V)+K(n+1)^k sqrt(E(V)).                 (SDL2)
```

The construction must use one finite set of Schur--Clifford **cell templates**
for the fixed contexts of `B_*`. The tape shift `U` supplies all levels by
conjugation; the polynomial factor in `(SDL2)` is allowed because it is
summable against `2^(-n)`. The accumulated packet itself need not remain
finite: one viable design has a nested Clifford tower `A_(n+1)=B_n` generated
self-similarly by the fixed cell template.

## Required local interface

1. `boolean-predicate-is-one-rank-jump` compiles each fixed BCS predicate.
2. Either build a growing tower with `A_(n+1)=B_n`, or provide a fixed-scale
   Morita transport turning the restricted `A_f` module back into the input
   type of the next `B_f` gate. Independent copies of one inclusion do not
   compose their multiplicities.
3. In the tower design, prove relative flexible exactification with constants
   uniform in the accumulated Clifford rank; the fixed-group theorem
   `finite-schur-clifford-packet-flexible-hs-exactification` alone has constants
   depending on the whole growing packet.
4. The exactified multiplicity belonging to `P_tilde_n` defines `a_n`, and
   overlap transport must make a fixed positive violation fraction pay the
   difference between `a_n` and `lambda a_(n+1)`.  The satisfying-oriented
   specialization has `lambda=1/2`; the balanced violation-oriented route may
   use any fixed `lambda<1`.

`finite-group-shared-overlap-polar-alignment` supplies the pairwise comparison
for every **fixed** common subgroup on a submodule of dimension
`d-O(eta^2d)`. The remaining part of clause 4 is narrowed further by
`shared-overlap-controls-packet-multiplicity-vector`, which charges the full
weighted type-vector discrepancy to the two discarded corners. It remains to
make this bound uniform along the growing tower, or to construct the
fixed-scale Morita bridge, and orient the restriction matrices so the result
is `(SDL2)`. The last step must use integral/rank information specific to
matrices; a trace-functorial comparison would violate
`trace-functorial-bcs-signal-groupification-impossible`.

## Attempts

- **Finite shift amalgam is the remaining syntax check.** The analytic
  one-cell modulus is now uniform and the type-vector recurrence is closed,
  but `toeplitz-schur-bcs-shift-amalgam` must still prove that the Fanizza
  shift and Toeplitz cell shift coexist in one finite presentation with an
  exact marked model. Without that theorem, the levelwise words are a family
  of compatible calculations rather than one group.

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
  recurrence cell. The new multiplicity-vector lemma already bounds every
  pairwise type discrepancy. Write the restriction matrices for the fixed
  predicates in that cell and check whether their signed composition has the
  required `1/2` coefficient on the marked type; any complementary type with
  nonzero return coefficient is the remaining leakage channel.
- **Fixed packet repeated without a bridge. Dead.** Restriction across
  `A_f<=B_f` outputs an `A_f`-module; a second independent copy of `B_f`
  expects another `B_f`-module. Identifying only the two `A_f` restrictions
  makes the constraints parallel and does not multiply the factor-two
  branching. Composition requires either `A_(n+1)=B_n` in a growing tower or
  a genuine Morita/holonomy return from `A_f` to `B_f`.
- **Growing tower. Active.** The Fanizza--Slofstra computation group already
  produces a self-similar sequence of Clifford pairs. Use one fixed local
  rank-gate template per cell and exactify only the new relative Pauli pair.
  The missing estimate is a Gowers--Hatami-style relative stability theorem
  whose constant is independent of the number of earlier Clifford pairs.
  `quantum-expander-rounds-relative-pauli-cell` proves the analytic estimate
  once a constant-gap expander on the old spin factor is exposed;
  `self-similar-clifford-quantum-expander-tape` is the remaining word-syntax
  input. Even after that, sequential compatibility and inactive-sector
  payment remain to be checked before `(SDL2)` is established.
