---
rg: 2
id: leavitt-central-sign-seed-proof
kind: route
title: Use the literal Leavitt transvection generator as the marked input to the central HNN construction
target: leavitt-central-sign-seed-for-lcs
requires:
  - thompson-steinberg-presentation-of-leavitt-unit-group
  - binary-leavitt-tracial-ultraproduct-images-are-trivial
  - central-hnn-tag-transfers-hyperlinear-radical
artifacts:
  - research/artifacts/liu-to-linear-games-and-marked-gap-2026-09-20.md
---

The first premise identifies x with 1+q, where q=S[00]T[01]. Prefix
cancellation gives q^2=0 and T[00]qS[01]=1. Thus q is nonzero and x is a
nonidentity involution in characteristic two. The second premise kills x in
every tracial matrix-ultraproduct homomorphism of this same group. Apply
the involution specialization of the third premise with w=x. Its displayed
presentation is exactly the six-generator/twenty-five-relator presentation
in the target. The associated subgroup is the finite group <x,J>=C2 times
C2, so no free-product doubling is needed.

The analytic contribution is Jihao Liu's internality theorem, and Andreas
Thom's conditional normalization in the imported whole-radical route.
The explicit source presentation has its separate Cairn/Bleak--Quick and
Steinberg completeness dependencies; this route does not replace them by
the observation that the relators hold in the Leavitt group.
