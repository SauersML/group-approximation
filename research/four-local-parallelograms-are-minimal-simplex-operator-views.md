---
rg: 2
id: four-local-parallelograms-are-minimal-simplex-operator-views
kind: claim
title: Four-point parallelograms are the first nonvacuous simplex-code operator views
distinct_from:
  bounded-template-average-blr-occurrence-decoder: that asks for the full robust operator-to-section theorem; this proves the sharp minimum arity and identifies the local relation it must use.
---

ESTABLISHED.  Let `C_n` be the affine simplex code on `F_2^n`.  On any set
of at most three distinct coordinates, the restriction map from `C_n` is
surjective.  Hence a local predicate depending on at most three distinguished
bits and accepting every affine table must accept every bit string: it can
test joint measurability, but it cannot impose any classical algebraic
relation.

Consequently, if all distinguished-coordinate views have arity at most three
and bounded coordinate incidence, their perfect-complete operator part is
subject to `bounded-cooccurrence-joint-pvms-do-not-round-globally`.  Such
views cannot by themselves decode arbitrary operator strategies to one global
simplex PVM.

Arity four is sharp.  Four distinct points are minimally affinely dependent
exactly when they form a parallelogram

```text
{x, x+a, x+b, x+a+b},                                      (FPM1)
```

and every affine word has even parity on `(FPM1)`.  Requiring one joint PVM
supported on the even-parity strings is therefore the first nonvacuous
perfect-complete operator view.  In particular it rejects the isolated
nonidentity sector used by the Pauli shield.

This does not assert that an arbitrary bounded-degree collection of
parallelograms is operator-sound.  The remaining minimal object is a
bounded-degree four-local parallelogram complex with **operator cosystolic
expansion**: small average parity/jointness defect must decode, on the same
Hilbert space, to global affine sections.  Once that decoding is available,
`expander-edge-overlay-detects-simplex-exterior-square` removes the Pauli
wedge and average BLR self-correction finishes the same-basis rounding.

