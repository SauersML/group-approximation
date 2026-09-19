---
rg: 2
id: effective-corner-host-higman-promotion
kind: claim
title: An effective recursive algebraic corner host already yields a finitely presented nonhyperlinear group
distinct_from:
  higman-bypass-needs-only-fg-recursive-nonhyperlinear: that begins with an abstract finitely generated recursively presented nonhyperlinear group; this extracts exactly such a group from the finite coefficient supports of an effective corner model.
  nonce-bcs-unital-algebraic-corner-map-forces-nonhyperlinear: that proves nonhyperlinearity of a given ambient host; this removes finite presentation of the host as a construction requirement.
---

Let `B` be a finitely generated unital star algebra with no CE tracial state.
It is enough to construct `(FSL1)` in an effectively recursively presented
group `Gamma`; `Gamma` itself need not be finitely generated or finitely
presented.  More explicitly, assume that `q` and the images of a finite
star-generating set of `B` are given as effective finite sums of words in the
recursive presentation of `Gamma`.  Then an explicit finitely presented
nonhyperlinear group can be produced.

Indeed, `finite-support-corner-localizes-obstruction` extracts from those
finite sums a finitely generated nonhyperlinear subgroup `Lambda`.  A
finitely generated subgroup of a recursively presented group is recursively
presented: enumerate all consequences of the ambient relators and output a
word in the chosen subgroup generators whenever its substituted ambient word
is proved trivial.  The explicit Higman embedding of
`higman-bypass-needs-only-fg-recursive-nonhyperlinear` then embeds `Lambda`
in a finitely presented group `H`.  Hyperlinearity is hereditary to
subgroups, so `H` is nonhyperlinear.

Thus finite presentability is not part of the signed-Hecke holonomy problem.
The live algebraic target may be weakened to an effective recursive group
with one finite-support corner model.  What cannot be weakened is the
load-bearing overlap itself: its finite support subgroup is already the
nonhyperlinear object.

For a finite BCS constraint algebra there is a stronger compactness fact.
`finite-bcs-corner-diagram-is-finitely-witnessed` shows that the finitely
many corner and defining-algebra identities already hold in a finite
subpresentation of the recursive host, with the corner still nonzero.  Thus
recursive presentation is a legitimate convenience, but an infinite tail
cannot be the mathematical source of the completed signed-Hecke chord.
