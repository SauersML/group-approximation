---
rg: 2
id: rectangular-safe-covariance-has-a-positive-head-absorber
kind: claim
title: Safe rectangular covariance admits exact positive-head finite absorbers
distinct_from:
  two-raw-unweighted-covariance-kills-jacobson-head: that shows identifying both raw orientations on one square occurrence kills the head; this keeps the two safe orientations on genuinely different source and target spaces
  two-raw-roots-have-a-uniform-full-carrier-gap: that controls distance to the full-carrier intertwiner space; this exhibits an exact rectangular full-carrier intertwiner with nonzero cokernel
  toeplitz-defect-needs-square-decoding: that identifies the abstract rectangular escape; this realizes it with arbitrary finite-group covariance and a prescribed positive head density
---

Let `F` be any finite group and let `beta:F->U(V)` be any unitary
representation. For every rational `alpha in (0,1)` there are
finite-dimensional spaces `H_S,H_T`, representations `pi_S,pi_T` of
`F`, an isometry `S:H_S->H_T`, its adjoint `T=S^*`, and a projection
`Q on H_T` such that

```text
TS=I_(H_S),                 ST=I_(H_T)-Q,               (RSC1)

QS=0,                       TQ=0,                       (RSC2)

pi_T(g)S=S pi_S(g)          for every g in F,           (RSC3)

rank(Q)/dim(H_T)=alpha.                                  (RSC4)
```

Thus every constant-core and both-raw-root covariance energy is exactly
zero: `S` already belongs to the full `F`-intertwiner space. Nevertheless
the rectangular Jacobson head `Q=I-ST` has prescribed positive density.

The associated head involution

```text
H_Q=I_(H_T)-2Q
```

satisfies

```text
||H_Q-I||_2^2=4 alpha.                                  (RSC5)
```

Hence the minimal packet retaining only the safe right-`S` and left-`T`
rows has exact finite-dimensional models with a macroscopic marked head.
No relative property-T or Hecke spectral gap can remove them, because the
survivor is an exact multiplicity-cokernel intertwiner rather than an
almost-invariant vector.

A successful redesign must add a same-trace/same-dimension authentication
or a reverse occurrence which makes the intertwiner square. The direct
unweighted reverse relation is unavailable: by
`two-raw-unweighted-covariance-kills-jacobson-head` it algebraically kills
the intended infinite head. This is the precise rectangular bottleneck.

DERIVATION
tensor-isometry-is-an-exact-bipartite-hecke-absorber-proof
