---
title: STW XXII finite Bratteli-cube trace-continuity audit (2026-08-30)
---

## New class

Take a finite tensor product of the changing matrix-to-UHF fields attached
to dense full-matrix chains, and then restrict it to any nonempty closed
subset `K` of

```text
X=(N union {infinity})^d.
```

The ambient cube has Cantor--Bendixson height `d+1`, so every closed
subspace has finite height at most `d+1`.  Fibres on the open stratum are
full matrices; every boundary face carries hyperfinite `II_1` fibres.
Closed subsets permit rooted finite-height patterns as well as the full
intersecting cube, so this is not a disjoint union of one-sequence examples.

## Completion check

All fibres sit in the common hyperfinite factor `bar-tensor_i R_i`.
Tensor products of the trace-preserving expectations onto the matrix stages
give the exact constrained section algebra.  A partition of unity in the
common `L^2` space, followed by Kaplansky approximation and those
expectations, proves uniform `2`-density of the original tensor-product
C*-algebra.  No local triviality or constant-fibre identification is used.

## Derived-subset lift

At any derivative stage, choose for each isolated point a nearest point in
the next derivative and apply the trace-preserving expectation from the
common hyperfinite factor into the isolated point's fibre.  Nearest points
approach every boundary limit.  Coordinatewise matrix expectations converge
to the identity whenever their coordinate tends to `infinity`, so this is
a contractive `2`-continuous extension.  Thus restriction is surjective on
section algebras and on norm/`2`-norm fibre gaps.

## Trace-free kernel

A positive class in the restriction kernel can be spectrally cut, modulo
the central norm-fibre ideal, so that it vanishes on the entire next face.
The exposed stratum is discrete.  At each of its points, Chebyshev's
estimate makes a fixed spectral support small enough to have arbitrarily
many orthogonal equivalent copies in the finite-factor fibre.  The
implementing unitaries may be chosen independently: multiplication by the
square root of the cut makes the resulting sections converge to zero at
the next face.  Boundedness of a trace then forces the cut, and hence the
original positive element, to have trace zero.

Finite descent reaches an isolated point, whose gap is zero.  Therefore
every gap is bounded-trace-free, and the exact fibre-gap criterion gives
the Problem XXII conclusion.

## Nontriviality and scope

Rank-one projections at the diagonal finite fibres define a nonzero top
gap because their norms stay one while their normalized `2`-norms tend to
zero.  Thus the result is not a consequence of equality of the two fibre
ideals.

The proof treats closed subfields of every finite product dimension `d`,
but not an infinite product.  At infinite Cantor--Bendixson height the finite derived-face
descent no longer terminates.

The later theorem
`stw22-dense-factor-fields-have-uniform-traces`
strictly enlarges the coordinate stages from full matrices to arbitrary
asymptotically dense nuclear unique-trace subalgebras.  The present audit is
retained as the finite-dimensional prototype where all expectations and
nonzero gap projections are completely explicit.
