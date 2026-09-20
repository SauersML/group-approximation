---
rg: 2
id: wave3-audit-symplectic-root-lift
kind: claim
title: Every commutative scalar CCKW matrix map lifts to the rank-two symplectic Steinberg group
distinct_from:
  wave3-visibility-cckw-matrix-maps-lift-to-steinberg: that concerns the stable linear Steinberg extension; this constructs lifts into the rank-two symplectic Steinberg group and treats central quotients without assuming its whole kernel is central.
artifacts:
  - research/artifacts/hyperbolic-rf-wave3-symplectic-lift-2026-09-20.md
---

For every commutative unital F7-algebra R and every x,y,z in R, the
homomorphism G=G_HB2(7) into ESp_4(R) given by

```
A=(I+x E03)(I+x E12),
B=(I+y E10)(I-y E23),
C=I+z E31
```

lifts to St(C2,R)=StSp_4(R), taking a,b,c to the root elements
X_(e1+e2)(x), X_(e2-e1)(y), X_(-2e2)(z), respectively.

Consequently every central extension of the actual image Q of K7
that admits a morphism from its preimage in St(C2,R), over Q,
pulls back to a split extension of K7. This includes every central
pushout defined by a conjugation-invariant homomorphism from the
Steinberg kernel. It excludes realization of the primitive canonical
class c0 modulo any integer m>1 by these extensions.

The assertion does not require the entire kernel of
St(C2,R)->ESp_4(R) to be central and does not assert it is central.
It does not cover arbitrary abstract central extensions of Q.

DERIVATION
wave3-audit-symplectic-root-lift-proof
