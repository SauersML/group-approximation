---
rg: 2
id: symmetrized-full-reset-forces-fixed-reynolds-density
kind: claim
title: The full Schur reset forces an explicit fixed-density Reynolds wall
distinct_from:
  predicate-rank-jump-forces-adjoint-reynolds-gap: that gives a quadratic lower bound from arbitrary forbidden Hilbert mass; this computes the exact wall after the finite full reset has fixed every packet multiplicity.
  residual-action-can-erase-local-reynolds-density: that shows an arbitrary residual action can destroy a local wall; this removes every erasing direction except action on one scalar multiplicity space.
  symmetrized-reset-collapses-schur-flow-to-one-ray: that computes the compatible representation-type ray; this computes the corresponding adjoint commutant codimension.
---

Let `f:{0,1}^k->{0,1}` be nonzero, let `C_f<=B_f` be the corrected
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
rank(E_C-E_B)=K_1 m^2,
d=L D m,
rank(E_C-E_B)/d^2=K_1/(L^2 D^2)>0,             (SFR1)
```

where `m` is the common multiplicity forced by the reset. In particular the
nonlinear predicate creates a fixed positive-density adjoint wall in every
nonzero exact reset representation, independently of ambient matrix
dimension.

For an approximate reset table, fixed-finite-group exactification changes the
named generator matrices and their Reynolds averages by `O(sqrt(E))`. Thus
the exact wall `(SFR1)` is available, up to the standard correction loss, for
any subsequent compressor or holonomy comparison.

The theorem does **not** assert that `(SFR1)` already survives in the
commutant of an uncontrolled group containing `B_f`. A residual group can
still act on the common multiplicity space of dimension `m`. What the reset
proves is that this scalar multiplicity action is now the only erasing
channel: there is no remaining selector, radical-character, or complementary
packet-type reservoir.
