---
rg: 2
id: finitely-generated-recursive-centralization-is-mf-compatible
kind: claim
title: A finitely generated compressed base and perfect commuting head can live in an amenable MF group
distinct_from:
  jacobson-two-braid-infimum-is-zero: that supplies an amenable quotient satisfying two specific braid words; this supplies a finitely generated compressed subgroup, its bilateral stable letter, and exact head-tail splitting without asserting those braid words.
  uniform-finitary-rank-compression-is-mf-compatible: that has a locally finite infinitely generated compressed subgroup with a rank bound; this makes the compressed subgroup itself finitely generated and exhibits exact finite-dimensional head collapse alongside MF models.
artifacts:
  - research/artifacts/finitely-generated-amenable-recursive-centralization-countermodel-2026-09-08.md
---

There is an explicit finitely generated amenable group `Gamma=<H,T>`
with `H` finitely generated and an embedded `D=GL_3(F_2)<=H` such that

```text
T H T^-1<=H,                  [D,T H T^-1]=1.
```

Every exact finite-dimensional unitary representation of `Gamma` kills
`D`. Nevertheless `Gamma` is operator MF, so an injective norm-corona
representation retains its nonidentity head involution `w=x_13,Q`.

The group `H` consists of permutations of seven one-sided rays that
eventually permute the rays and translate them by integers of total
sum zero. Head permutations, global ray permutations, and six explicit
ray transfers generate it. Uniform unilateral translation induces an
injective endomorphism fixing the head pointwise. Extending the action
to bilateral rays realizes it by the genuine permutation `T`.

There is also a finite head-tail packet `G_Q x G_P`, where the tail
acts by the same seven-point permutation at every positive level.
Writing `tau(g)=T g_Q T^-1` and `delta(g)=T g_P T^-1` gives

```text
g_P=tau(g)delta(g),             [tau(G),delta(G)]=1,
```

and the same identities at every shift.

Thus finite generation, recursive centralization, and this exact
head-tail splitting alone do not force a uniform matrix gap. No
realization of the Jacobson six-coordinate packet, full boundary
packet, or remaining mixed words is asserted. Their positive-gap
problem is not refuted by this comparison.

The MF conclusion uses the published amenable-group theorem, explicitly
recorded as a literature input; it is not newly kernel-formalized here.

DERIVATION
seven-ray-recursive-centralization-countermodel-proof
