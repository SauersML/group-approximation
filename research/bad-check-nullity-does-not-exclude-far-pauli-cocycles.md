---
rg: 2
id: bad-check-nullity-does-not-exclude-far-pauli-cocycles
kind: claim
title: A vanishing bad-check nullity budget can still carry far sparse Pauli cocycles
distinct_from:
  central-clifford-parity-sectors-round-uniformly: that assumes every parity check is exact and forces every nonzero scalar-sign sector to have constant complete-pair energy; this shows why deleting a vanishing fraction of checks cannot be handled only by counting the resulting extra kernel dimension.
  sparse-clifford-cycles-refute-average-commutator-rounding: that uses a full-rank cycle cocycle; this gives rank `O(1/eta)` cocycles fitting inside an `eta L` bad-check nullity budget while retaining constant rounding distance.
  positive-rate-tanner-tests-have-contextual-models: that counts the full exterior-square quotient of a positive-rate local code; this is a low-rank asymptotic valley tailored to the balanced-overlay bad-check scale.
---

Let `eta_L->0` with `eta_L^2 L->infinity`.  There are alternating matrices
`B_L over F_2`, of size `L`, such that

```text
rank(B_L)=O(1/eta_L),
(1/L^2)|{(i,j):B_L(i,j)=1}|=Theta(eta_L),                 (BCN1)
```

but every Pauli-reflection realization `(Q_i)` of the commutation table

```text
Q_iQ_j=(-1)^(B_L(i,j))Q_jQ_i                             (BCN2)
```

has average squared normalized-HS distance bounded below by a numerical
constant from every commuting reflection tuple.

Since `rank(B_L)=o(eta_L L)`, this cocycle fits in the amount of extra linear
space that can be created by deleting `eta_L L` independent parity checks.
Therefore the following proposed far-valley argument is invalid:

```text
only eta L parity rows are bad
=> the enlarged parity kernel has only eta L extra dimensions
=> every projective cocycle is close to the exact-parity sectors.          (BCN3)
```

Balanced original-check density is necessary but rank/nullity bookkeeping
is not sufficient.  To exclude projective far valleys in
`balanced-overlay-diffuse-square-function-newton`, one needs a geometric
erasure-cleaning statement: cocycle rows whose syndromes are supported on a
small check set must be supported, modulo the original code, on a small
common **coordinate** set.  Ordinary dimension loss under row deletion does
not provide that localization.

This construction is an algebraic capacity obstruction, not itself a
countermodel to the selected balanced Tanner system: it does not assert that
the required cocycle row space occurs after deleting actual checks of that
system.  It identifies the exact additional property a proof must consume.

