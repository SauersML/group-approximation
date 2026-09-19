---
rg: 2
id: property-t-free-leavitt-via-finite-multiplicity-certificate
kind: route
title: Annihilate the distinguished root with one finite packet multiplicity certificate
target: property-t-free-leavitt-full-mf-radical
requires:
  - leavitt-prefix-packet-pressure-certificate
  - finite-packet-multiplicity-certificates-detect-mf-radicals
  - full-leavitt-idempotent-defect-saturation
---

**INVALIDATED.**  The required packet certificate cannot be obtained from
the stated finite-group functoriality relations.  The strictly positive
regular profile of
`finite-packet-functoriality-has-positive-regular-profile` satisfies all of
them while retaining every irreducible type.

Let a norm-corona representation of the binary-Leavitt elementary group be
given.  Exactify the finite depth-one/depth-two packet diagram from
`leavitt-prefix-packet-pressure-certificate` on a
common coordinate tail.  The certificate `(LPC1)` and
`finite-packet-multiplicity-certificates-detect-mf-radicals` kill every
irreducible packet type on which the distinguished root `z` acts
nontrivially.  Hence the corona representation sends `z` to the identity.

Thus `z` belongs to the MF radical.  The two elementary commutators in
`full-leavitt-idempotent-defect-saturation` put a complete root subgroup in
the normal closure of `z`, and Weyl conjugacy supplies all root subgroups.
Therefore `z` normally generates the elementary group.  Normality of the MF
radical now gives full MF collapse.
