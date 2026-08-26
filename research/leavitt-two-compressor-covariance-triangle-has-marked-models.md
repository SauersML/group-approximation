---
rg: 2
id: leavitt-two-compressor-covariance-triangle-has-marked-models
kind: claim
title: Two-compressor covariance and its order-three triangle have marked finite models
artifacts:
  - research/leavitt-two-compressor-permutation-model-proof.md
distinct_from:
  leavitt-el20-two-compressor-fd-representations-kill-mark: that uses the full infinite diagonal group and both conjugate child algebras in one exact finite-dimensional representation; this models every fixed finite diagonal stage and the obvious mixed triangle while retaining the mark.
  finite-positive-root-fragments-have-marked-regular-models: that treats positive-root fragments without the complementary compressor covariance or relative order-three word.
---

For every finite diagonal stage `H=Lambda_k`, there is an exact permutation
model of the abstract two-child covariance table in which the relative
compressor has order three and every nontrivial marked involution has
operator-norm distance two from the identity.

Consequently the two self-copy equations, commutation of the complementary
children, and the elementary-matrix relation
`(tau_1 tau_0^(-1))^3=1` do not yield an operator-norm MF obstruction.  A
successful two-compressor proof must use another literal relation in the
concrete group.  No corresponding order-three identity is asserted for
arbitrary Steinberg lifts.

The first such missing relations are now explicit:
`leavitt-two-compressor-core-has-modular-normal-form` supplies the order-two
word `(tau_1 tau_0^(-2))^2`, while
`leavitt-two-compressor-depth-two-relation-breaks-hxh-model` supplies the
recursive child split.  Thus this claim is a finite-packet fence, not a model
of the literal full subgroup.

DERIVATION
leavitt-two-compressor-permutation-model-proof
