---
rg: 2
id: full-mf-radical-uniform-asymptotic-collapse-proof
kind: route
title: Pass between asymptotic representations and their corona homomorphisms
target: full-mf-radical-uniform-asymptotic-collapse
requires:
  - universal-mf-quotient
  - hilbert-hotel-model-full-mf-radical
---

An operator-norm asymptotic representation defines a homomorphism to its
norm matrix corona.  An element lies in its kernel exactly when its unitary
lifts converge to the identity in operator norm.

Thus total radical makes every asymptotic representation pointwise trivial.
Conversely, applying pointwise triviality to coordinate lifts of an arbitrary
corona homomorphism shows that homomorphism is trivial.  Closeness to the
trivial exact representation is precisely matricial stability.

If the finite challenge failed, exhaust `G` by finite sets `E_n`, take error
`1/n`, and choose violating maps.  A subsequence keeps one element of the
fixed finite set `F` uniformly away from the identity.  These maps form an
asymptotic representation, contradicting pointwise collapse.
