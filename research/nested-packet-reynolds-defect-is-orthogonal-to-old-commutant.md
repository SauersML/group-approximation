---
rg: 2
id: nested-packet-reynolds-defect-is-orthogonal-to-old-commutant
kind: claim
title: A transported nested-packet Reynolds defect is orthogonal to the old commutant
distinct_from:
  packet-kazhdan-commutant-placement-decouples: that separates the packet and Kazhdan actions on tensor factors; this obstruction holds even when the packet is genuinely nested inside the old group.
  adjoint-reynolds-rank-gap-pays-every-return: that compares the dimensions of a Reynolds range and an arbitrary returned copy; this identifies a whole class of returns whose overlap with the old commutant is exactly zero.
  finite-normalizer-covariance-density-no-go: that dilutes density through finite regular quotients; this is a representation-by-representation orthogonality identity with no residual-finiteness hypothesis.
---

Let `rho:Lambda->U(H)` be a finite-dimensional unitary representation and
let `A<B<Lambda` be finite subgroups.  Write `R_A,R_B` for conjugation
Reynolds projections on `End(H)`, and let `E_Lambda` be the orthogonal
projection onto `End_Lambda(H)`.  Then

```text
E_Lambda <= R_B <= R_A,
(R_A-R_B)E_Lambda=E_Lambda(R_A-R_B)=0.                 (NRO1)
```

More generally, suppose `rho` extends to an ambient group containing an
element `t` with

```text
t B t^(-1) < Lambda.
```

For `T=Ad_(rho(t))`,

```text
T(R_A-R_B)T^* perpendicular to End_Lambda(H).          (NRO2)
```

Thus ordinary group-word conjugacy cannot place the raw positive-density
Schur Reynolds defect in the old commutant.  This remains true when the
packet is not tensor-decoupled: transporting the full packet into the old
group transports its defect into the orthogonal complement of the old
fixed space.

If an inverse-closed generating set of `Lambda` has adjoint Laplacian
`Delta_Lambda` with gap `kappa` off `End_Lambda(H)`, then every
`X` in the range in `(NRO2)` satisfies

```text
<X,Delta_Lambda X> >= kappa ||X||_2^2.                 (NRO3)
```

Consequently a proof of
`parity-compressor-old-commutant-has-positive-density` cannot use a unitary
transporter which merely conjugates the nested packet table (or its whole
Reynolds difference) into `Lambda`.  It must use a genuinely different
operation: a partial/compressed coefficient, a scalar overlap which does
not transport the full `B` action, or a matrix-only one-sided mechanism.
