# Non-hyperlinear finite memory: macroscopic self-copy and Reynolds atoms

## Status

This audit records three proved reductions and two open interfaces.  It does
not claim a non-hyperlinear group.

The current public benchmark remains Taller--Vidick, arXiv:2507.22444v2:
their abstract states that upgrading their almost-perfect LCS hardness result
to perfect completeness would imply a non-hyperlinear group.

## What was genuinely new

1. `tracial-superoperator-self-copy-has-no-macroscopic-excess` proves, without
   property `(T)`, that a one-sided self-copy has equal parent and child
   zero-energy projections in the adjoint tracial ultraproduct.  It is the
   qualitative macroscopic theorem; Cairn's existing
   `property-t-hs-positive-density-commutant-no-growth` remains the stronger
   quantitative finite-stage theorem when a Kazhdan gap is available.
2. `central-sign-bcs-atoms-are-subgroup-reynolds-projections` identifies every
   Boolean assignment atom with `e_(H_a)Q_-`.  This removes the nonlinear
   truth-table router only at the projection-naming stage.
3. `central-sign-reynolds-atoms-have-fixed-canonical-density` computes
   `tau(e_(H_a)Q_-)=2^(-(k+1))` whenever the full context packet embeds.
   Thus canonical microstates already see every individual atom at fixed
   positive density; the non-CE game gap is not a density amplifier.

## What Cairn already contained

The proposed algebraic-Haar compiler is already
`algebraic-compact-action-group-factor-compiler`.  Moreover
`ALGEBRAIC_HAAR_NONCE_TO_NONHYPERLINEAR.md` proves that Manzoor's free-group
source cannot instantiate it: an abelian-by-sofic semidirect product is
sofic and hence hyperlinear.

The proposed Cartan-preserving Bernoulli compiler is already represented by
`coherent-bernoulli-actor-tables-are-cartan-soficity`,
`lamp-charts-recover-set-action`, and the invariant-Cartan branch.  It was not
duplicated.

The binary reflection trace formula is part of Cairn's existing binary-face
and overlap calculus.  It is useful local algebra but does not encode a
nonlinear predicate or remove regular companion sectors, so it was not made
into another endpoint.

## The remaining regular-safe interface

For a context of commuting involutions `x_i`, a central involution `J`, and
`a in F_2^k`, set

```text
H_a=<x_i J^(a_i)>.
```

On `Q_-=(1-J)/2`, the subgroup Reynolds projection is exactly the assignment
atom.  Cairn's subgroup-Hecke HNN actuator can pay a reverse fixed-space gap,
but an injection `K->H` always obeys the regular orientation

```text
tau(e_H)=1/|H| <= 1/|K|=tau(e_K).
```

Thus any positive selected-sector gap has companion mass elsewhere.  A fixed
packet, one HNN edge, or a finite stationary cycle cannot remove it.

The live target `central-sign-reynolds-first-hit-compiler` asks for the
companion mass to be routed into successive first-hit layers in finite matrix
models.  The initial lower bound is already the canonical atom density above.
The robust finite-dimensional BCS gap must instead supply the operator-valued
selection which makes the exit law hold in matrices but fail for the regular
compensation flow.  The qualification “finite matrix” is essential.  Cairn
already proves that an exact trace-functorial infinite first-hit ladder kills
its carrier in the canonical group von Neumann algebra.

Once the compiler supplies fixed `q_*,eta>0`, the established first-hit ledger
gives

```text
eta N q_* <= 1 + controlled presentation error.
```

A sufficiently large fixed `N` yields a normalized-HS defect floor.  No new
matrix inequality remains after that interface.
