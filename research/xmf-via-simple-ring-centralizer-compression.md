---
rg: 2
id: xmf-via-simple-ring-centralizer-compression
kind: route
title: Elementary group of a simple ring with a centralizer-compressing automorphism
target: mf-kazhdan-quotientless-mapping-torus-exact-radical
requires:
  - simple-ring-centralizer-compression-gives-xmf
  - simple-ring-with-centralizer-compressing-automorphism
---

## Why sufficient

`simple-ring-with-centralizer-compressing-automorphism` supplies `(S, sigma,
R, z)` with (G1) and (G2), which are exactly the hypotheses (CC1)--(CC4) of
`simple-ring-centralizer-compression-gives-xmf`.  That theorem outputs
`Q = EL_3(S)` and `psi = sigma` satisfying `(XMF)`.

The route instantiates the compression recipe of Attempt 3 of the target:
- the source is `L = EL_3(R)`, contracted by the generator of `Z`;
- the root is the scalar `zI`;
- saturation comes from simplicity of `S` through the Steinberg commutator
  relations.

The only open input is the ring gate.
