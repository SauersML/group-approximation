---
rg: 2
id: regular-dyadic-mackey-capacity-proof
kind: route
title: Conjugate-double every finite sector inside an amplified regular block
target: regular-dyadic-windows-have-unlimited-conjugate-mackey-capacity
requires:
  - cartantype-mackey-cocycle-is-pauli-and-locally-absorbed
  - finite-regular-adjoint-retains-full-conductor
---

On matrix units `E_(x,y)` of `End(l^2 Q)`, diagonal left translation acts
by

```text
(lambda_Q tensor conjugate(lambda_Q))(g) E_(x,y)
 =E_(gx,gy).                                             (RMC3)
```

The invariant `x^(-1)y` labels `|Q|` free orbits, proving `(RMC2)`.
The trace is therefore the regular trace and every nonidentity element
still has trace zero.  Faithfulness, hence the full congruence conductor,
is retained.

For the finite sector groupoid, scalar factors in
`C_h C_g=c(h,g)C_(hg)` cancel against their complex conjugates, so `(RMC1)`
is an honest functor simultaneously on all arrows.  Tensoring carrier
projections and partial intertwiners with their conjugates preserves all
normalized trace ratios after the regular amplification `(RMC2)`.

These identities are pointwise in the matrix level.  Hence the finite
groupoid may grow with the approximation index: at each index its finite
conjugate double exists, and no uniform dimension ceiling is among the
hyperlinear-microstate requirements.

For the numerical comparison, a scalar cocycle on a finite group of order
`M` has irreducible projective dimension at most `sqrt(M)`, because the sum
of squared twisted-irreducible dimensions is `M`.  On the repeated Cartan
type, taking `M<=16^k` gives
`2^(2k)`.  The smooth congruence kernel of one level in `SL_3` has dimension
eight, so the order ratio over `2k` levels is `2^(8*2k)=2^(16k)`, proving
`(RMC4)`.
