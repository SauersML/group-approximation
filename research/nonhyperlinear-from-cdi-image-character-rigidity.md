---
rg: 2
id: nonhyperlinear-from-cdi-image-character-rigidity
kind: route
title: Apply character rigidity only after dividing by the actual CDI kernel
target: non-hyperlinear-group
requires:
  - cdi-image-quotient-off-regular-characters-are-ce
  - cdi-character-rigid-image-quotient-is-an-exact-bridge
---

Apply `cdi-character-rigid-image-quotient-is-an-exact-bridge` to the fixed
non-CE input and its CDI representation.  The open hypothesis forces the
faithful image character to be regular, hence identifies its non-CE factor
`Q` trace-preservingly with `L(H/ker(pi))`.  Therefore the countable image
quotient is nonhyperlinear.

The permanence audit
`standard-permanence-does-not-rigidify-the-cdi-image` explains why the open
hypothesis cannot be replaced formally by character rigidity of a chosen
quotient, product, extension, subgroup, or induced representation.
