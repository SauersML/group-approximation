---
rg: 2
id: schur-commutator-tag-is-not-fresh-under-selector-transport
kind: claim
title: Transporting a Schur selector chart forces its commutator tag to remain an affine selector word
distinct_from:
  context-atom-tag-bridge-installs-child-carrier: that gives the projection identity when the displayed source and target tables exist; this proves that the Schur application cannot treat the first target tag as independent while transporting the selector tuple.
  tensor-affine-selector-pattern-barrier: that forbids tensor-independent affine selectors for nonlinear predicates in general; this is the exact HNN compatibility obstruction for the proposed S3 endpoint bridge.
---

**ESTABLISHED.**  Let `P_a,Q_a` be fixed words in a class-two
Schur--Clifford packet with central selector group

```text
D=<J,z_1,...,z_k>.
```

Then their commutator is a fixed affine selector word

```text
K_a=[P_a,Q_a]=J^c product_i z_i^(r_i).                 (SCT1)
```

Suppose a proposed context bridge transports the literal selector tuple and
the endpoint commutator by

```text
uJu^*=J,
uz_i u^*=z'_i,
uK_a u^*=T_1.                                         (SCT2)
```

The bridge relations force

```text
T_1=J^c product_i (z'_i)^(r_i).                        (SCT3)
```

Consequently `T_1` is not a fresh independent tag bit.  On a transported
assignment atom it has the predetermined sign of the affine character in
`(SCT3)`.  In particular the two-bit endpoint-to-tag calculation may still
be evaluated on that atom, but it supplies at most the other independent tag
bit there; it does not create a fresh two-bit table over the whole successor
context.

There is therefore a strict dichotomy for the proposed S3 bridge:

1. transport only `<J,K_a,b_a>` to a fresh tag square, in which case
   `two-bit-tag-routing-splits-s3-exit-and-survivor` applies but no selector
   atom or shared context carrier is transported; or
2. transport the selector chart as well, in which case `(SCT3)` holds and
   the first tag is context-affine rather than a common independent pulse.

Requiring this context-affine word to commute with all variables of every
other successor context adds cross-context relations not present in the BCS.
No robust shared-BCS gap or exact marked model may be invoked after adding
those relations without a separate preservation theorem.

Proof: `schur-commutator-tag-selector-dependence-proof`.
