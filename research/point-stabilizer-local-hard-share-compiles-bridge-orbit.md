---
rg: 2
id: point-stabilizer-local-hard-share-compiles-bridge-orbit
kind: claim
title: One point-stabilizer-local hard share finitely compiles the whole prefix-preserving bridge orbit
distinct_from:
  gauge-covariant-hard-shares-admit-site-bridges: that constructs bridge unitaries independently in an exact marked representation; this gives finite group syntax and polynomial derivation bounds when the source share is a site occurrence.
  finite-orbit-occurrence-pauli-compiler: that must compile a whole unbounded robust game family; this compiles one unary bridge role and one off-diagonal commutator orbit.
  stabilizer-generator-control-has-unbounded-address-loss: that rules out a uniform address-independent modulus; this needs only polynomial loss in the recurrence level and records it explicitly.
---

Let a finitely presented group contain Thompson `V` acting on the rational-tail
orbit `X`, the independent pulse signs `a_x,B_x`, and an involution `A_0`
attached to a base site `x_0`.  Assume the finitely generated point stabilizer
`V_(x_0)` fixes `A_0`.  Put

```text
A_x=g A_0 g^-1                     when g x_0=x.       (PSB1)
```

This is independent of `g`.  Adjoin one unitary generator `u_0` and finitely
many relations

```text
[u_0,h_i]=1                         (h_i generating V_(x_0)),
a_(x_0)u_0=u_0A_0,
[u_0,B_(y_0)]=1                     (one y_0!=x_0).     (PSB2)
```

For `u_x=g u_0g^-1`, the resulting finitely presented group satisfies

```text
a_xu_x=u_xA_x,
[u_x,B_y]=1                         (x!=y).             (PSB3)
```

If the standard prefix-table transporters and point-stabilizer normal forms
for the chosen sites have polynomial length, then every level-`n` instance of
`(PSB3)` has polynomial van Kampen area in the finite presentation.  Combined
with `prefix-preserving-two-step-hard-bridge-localizes-exit`, this supplies the
required polynomial HS prefix estimate.

For exact completeness it is enough that the marked witness be a site tensor
representation in which `A_0` and `a_(x_0)` are balanced involutions on the
base-site factor and `V_(x_0)` fixes that factor pointwise.  Then choose `u_0`
on that factor by spectral matching; all relations `(PSB2)` hold and their
`V` conjugates give the simultaneous bridge family.
