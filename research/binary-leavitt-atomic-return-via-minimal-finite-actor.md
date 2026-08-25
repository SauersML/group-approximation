---
rg: 2
id: binary-leavitt-atomic-return-via-minimal-finite-actor
kind: route
title: Exactify a finite root window and return a least-rank character atom through its finite actor orbit
target: binary-leavitt-atomic-morita-return
requires:
  - norm-corona-sparse-character-atom-reduces-pointwise-centralizer
  - binary-leavitt-minimal-atom-finite-actor-compiler
---

Choose a finite elementary abelian root window containing the marked
involution and exactify it in operator norm.  Exactify a finite normalizer
packet, select a nonzero marked character atom having least rank in its
finite actor orbit, and apply the proposed finite-actor compiler to return
the two branch transports to this atom.  The asserted inverse and
completeness rows would be `(BLAMR)`.

This route is invalidated by
`binary-leavitt-finite-actor-minimal-atom-dichotomy`: finite normalizer
covariance has exact crossed-product models with a surviving minimal atom
and no binary Leavitt capacity.

