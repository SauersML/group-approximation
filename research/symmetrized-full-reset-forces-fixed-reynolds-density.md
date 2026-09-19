---
rg: 2
id: symmetrized-full-reset-forces-fixed-reynolds-density
kind: claim
title: The full Schur reset forces a fixed-density child/full Reynolds wall
distinct_from:
  predicate-rank-jump-forces-adjoint-reynolds-gap: that gives a predicate-sensitive quadratic lower bound from forbidden Hilbert mass; this computes the exact structural child/full wall after the finite reset and records that it is not itself predicate-sensitive.
  residual-action-can-erase-local-reynolds-density: that shows an arbitrary residual action can destroy a local wall; this removes every erasing direction except action on one scalar multiplicity space.
  symmetrized-reset-collapses-schur-flow-to-one-ray: that computes the compatible representation-type ray; this computes the corresponding adjoint commutant codimension.
---

Let `f:{0,1}^k->{0,1}` be nonconstant, let `C_f<=B_f` be the corrected
Schur child/full-packet inclusion, and put

```text
D=2^N,   K_1=|f^(-1)(1)|,   K_0=|f^(-1)(0)|,
L=2^(k+1)=2(K_0+K_1).
```

Let `rho` be an exact `J=-1` representation of the finite full reset
`Rhat_f` from `translation-symmetrized-full-schur-reset`, of dimension `d`.
Write `E_C,E_B` for the Reynolds orthogonal projections on `End(H)` obtained
by averaging conjugation over `rho(C_f)` and `rho(B_f)`. Then

```text
rank(E_C-E_B)=2L n^2,
d=2L D n,
rank(E_C-E_B)/d^2=1/(2 L D^2)>0.               (SFR1)
```

where `n` is the common multiplicity scale forced by the reset. In particular
the child/full inclusion has a fixed positive-density adjoint wall in every
nonzero exact reset representation, independently of ambient matrix
dimension.

This exact density is **structural, not predicate-sensitive**: the inactive
radical splitting contributes the same child/full commutant loss as the
active Pauli block. The nonlinear information remains instead in the exact
restriction-multiplicity surplus `2K_1n` of `(SRC7)`. Consequently `(SFR1)`
is a ready-made positive-density carrier, but a global return still has to
couple its orientation to that surplus; the bare rank of the wall cannot
distinguish `f=0` from `f=1`.

For an approximate reset table, fixed-finite-group exactification changes the
named generator matrices and their Reynolds averages by `O(sqrt(E))`. Thus
the exact wall `(SFR1)` is available, up to the standard correction loss, for
any subsequent compressor or holonomy comparison.

The theorem does **not** assert that `(SFR1)` already survives in the
commutant of an uncontrolled group containing `B_f`. A residual group can
still act on the common multiplicity space of dimension `n`. What the reset
proves is that this scalar multiplicity action is now the only erasing
channel: there is no remaining selector, radical-character, or complementary
packet-type reservoir.
