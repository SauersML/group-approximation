---
rg: 2
id: opnorm-native-cross-gram-does-not-promote-to-hyperlinearity
kind: claim
title: The operator-norm native cross-Gram theorem does not by itself exclude hyperlinear microstates
invalidates:
  - nonhyperlinear-from-binary-leavitt-native-cross-gram
artifacts:
  - research/opnorm-native-cross-gram-scope-proof.md
distinct_from:
  opnorm-return-row-cannot-come-from-an-hs-ledger: that compares operator and Hilbert--Schmidt norms for one rank-deficient support row; this records the quantifier mismatch for the native occurrence theorem itself.
  binary-leavitt-native-two-scale-cross-gram-positive: that proves the occurrence estimate on reblocked operator-norm MF microstates; this prevents changing its domain to arbitrary canonical HS microstates after the fact.
---

The established route into
`binary-leavitt-native-two-scale-cross-gram-positive` starts with an
operator-norm asymptotic representation, applies operator-norm packet
exactification, and uses the active-core reblocking available in a norm
matrix corona.  Its conclusion is therefore an operator-norm MF-radical
statement.

A hyperlinear approximation supplies only normalized-Hilbert--Schmidt
relator control and canonical trace moments.  It does not satisfy that
operator-norm hypothesis.  Consequently one may not apply `(NCG1)` to a
canonical hyperlinear microstate merely because its marked involution has a
trace-one-half negative carrier.  The route
`nonhyperlinear-from-binary-leavitt-native-cross-gram` makes exactly this
unsupported substitution and is invalid.

This is only a scope fence.  It does not assert that an HS analogue of the
same-center occurrence theorem is false.  Proving such an analogue, with
all occurrence errors controlled in normalized HS norm on canonical
microstates, would be a separate theorem.  No such input belongs to the
Property-T-free MF manuscript endpoint proved here.

DERIVATION
opnorm-native-cross-gram-scope-proof
