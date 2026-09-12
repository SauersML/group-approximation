---
rg: 2
id: jacobson-shift-surviving-head-has-a-tracial-core
kind: claim
title: A surviving recursive Jacobson head has a tracial matrix model with at least one-quarter active density
distinct_from:
  jacobson-shift-head-dies-in-amenable-targets: that excludes amenable marked images; this turns an arbitrary surviving norm-corona image into a tracial image faithful on the simple finitary kernel.
  jacobson-shift-mixed-gap: that asks for operator-norm collapse in all dimensions; this supplies a necessary positive-density tracial model if that collapse fails.
artifacts:
  - research/artifacts/jacobson-surviving-head-has-a-tracial-core-2026-09-08.md
---

Let `Gamma=Theta_shift`, let `w=x_13,Q`, and let `pi` be its
literal bilateral action. If a norm-corona homomorphism `rho`
retains `w`, there is a homomorphism `psi` into a tracial matrix
ultraproduct, represented by normalized-Hilbert--Schmidt asymptotic
maps `W_n:Gamma->U(k_n)`, with

```text
W_n(w)^2=I,
rank(W_n(w)-I)/k_n>=1/4,
||psi(w)-1||_2>=1,
ker(rho)<=ker(psi)<=ker(pi).
```

The map `psi` is injective on the simple normal finitary subgroup
`L=normalClosure(w)`. It need not be injective on `Gamma`, and
the resulting surjection `psi(Gamma)->pi(Gamma)` does not prove
hyperlinearity of the literal quotient. No contradiction to the
existence of `psi` is established.

DERIVATION
jacobson-shift-support-bound-tracial-core-proof
