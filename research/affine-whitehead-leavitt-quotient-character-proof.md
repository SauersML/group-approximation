---
rg: 2
id: affine-whitehead-leavitt-quotient-character-proof
kind: route
title: Centralize the active head, project one Wedderburn block, and pull back the regular character
target: affine-whitehead-has-leavitt-quotient-character-face
requires:
  - affine-active-corner-has-faithful-binary-leavitt-envelope
  - coefficient-central-affine-leavitt-envelope-is-morita-trivial
  - d-ary-leavitt-groups-nonsofic-over-finite-fields
  - full-signed-whitehead-amalgam-has-fd-invisible-clifford-mark
  - sl3-amenable-base-has-delocalized-rigid-factor
---

The support relations make `1-A` a central coefficient summand.  On the
active summand, impose coefficient centrality and use the two active
Wedderburn blocks.  This gives a ring epimorphism onto
`M_3(L_2(k)) times M_3(L_2(k))`, hence a group epimorphism from the Steinberg
group onto the product of the two elementary groups.  The explicit
Whitehead matrix has fourth power one in each elementary factor, so the map
descends through `normalClosure(W^4)`.

Each coordinate kernel maps onto the other infinite factor.  Apply the
exchange-ring normal-subgroup sandwich theorem to the purely infinite simple
Morita amplification `M_3(L_2(k))`; the elementary group modulo its center is
infinite simple and hence ICC.  Pulling back its regular character proves the
factor-character assertion.

Property `(T)` passes from the corresponding Steinberg group to the elementary
and central quotients.  Thus a CE instance of this character would be
nonhyperfinite, locating the exact ordinary-Leavitt hypothesis hidden in any
purported CE-character collapse theorem.
