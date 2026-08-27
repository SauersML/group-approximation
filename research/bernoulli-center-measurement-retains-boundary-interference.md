---
rg: 2
id: bernoulli-center-measurement-retains-boundary-interference
kind: claim
title: Exact Bernoulli center measurements retain a thirty-five-over-seventy-two inverse-composition defect
invalidates:
  - two-site-coupling-route-to-a5-classicalization
distinct_from:
  two-site-center-measurement-interference-is-relator-paid: that asks actor relator energy to control the sequential-measurement interference; this computes a zero-relator canonical model with a fixed positive interference floor.
  scalar-trace-of-diagonal-normalizer-is-permutation-blind: that hides a phase inside a normalizer of a fixed diagonal algebra; this obstruction is classical boundary information loss under conditional expectation.
---

Let `z` be the rational five-dimensional `A5` central idempotent, with
Bernoulli mass

```text
q=tau(z)=5/12.
```

In the canonical group trace of an `A5` generalized wreath product, choose a
site `p` and an actor element `g` with `gp!=p`.  Use the two-atom PVM
`(1-z_p,z_p)`.  The block-mass coupling of the exact actor unitary `u_g` is

```text
C_g=mu tensor mu,             mu=(1-q,q),              (BCI1)
```

because the lamp center variables at `p` and `g^(-1)p` are independent.
The same holds for `g^(-1)`.  Consequently

```text
C_g o_mu C_(g^(-1))=mu tensor mu,                     (BCI2)
```

whereas the identity coupling is `Diag(mu)`.  With total variation equal to
one half of the entrywise `l1` norm,

```text
||mu tensor mu-Diag(mu)||_TV
 =2q(1-q)=35/72.                                      (BCI3)
```

All group relations and all canonical mixed cylinder moments are exact in
this model.  Therefore no estimate can bound the left side of `(TMI3)` by
presentation defect for a fixed finite center PVM.  Enlarging to a finite
site set merely moves the same loss to its actor boundary; composing a shift
with its inverse forgets every coordinate which left the measured window.

This does not refute `two-site-a5-center-classicalization`.  It refutes only
the attempt to obtain its actor permutations by successively measuring one
fixed finite lamp-center PVM.  A live construction must retain boundary
labels in an enlarged path/state carrier, or classicalize the actor and the
growing lamp field jointly without inserting a lossy conditional
expectation between products.

