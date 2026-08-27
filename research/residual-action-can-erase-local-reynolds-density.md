---
rg: 2
id: residual-action-can-erase-local-reynolds-density
kind: claim
title: An uncontrolled residual action can erase the density of a locally placed packet Reynolds gap
distinct_from:
  packet-kazhdan-commutant-placement-decouples: that refutes bare tensor-factor commutation with the two compressor sides; this quantifies the opposite failure, where the residual compressed action fills the packet multiplicity algebra and shrinks the local gap to zero density.
  commutant-density-trace-blind: that computes vanishing commutant density in regular-character limits; this is a finite-dimensional tensor calculation applying directly to a finite packet child/full inclusion.
---

Let `H<B` be any fixed finite packet inclusion with a nonzero Reynolds gap on
a fixed packet space `K`. On

```text
K tensor C^m
```

the local inclusion `H<B` has Reynolds-gap rank proportional to `m^2`.
However, if the residual compressed group generates `M_m(C)` on the second
factor, the relevant enlarged algebras are

```text
Alg(H) tensor M_m(C) < Alg(B) tensor M_m(C).                    (REA1)
```

Their commutant difference has rank independent of `m`; divided by
`(dim(K)m)^2`, its adjoint density tends to zero.

Consequently the algebraic facts

```text
H <= alpha(Gamma),             B <= Gamma
```

do not imply that the packet Reynolds difference lies in
`Comm(alpha(Gamma)) minus Comm(Gamma)` with positive density. Any completion
of `schur-packet-as-positive-density-compressor-wall` must control the
residual action on packet multiplicity, or recursively reapply the packet
inside its residual commutant. The Toeplitz compressor supplies an explicit
head-tail substrate for the latter option but does not by itself prove the
required retention.

