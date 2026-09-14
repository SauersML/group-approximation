---
rg: 2
id: kun-thom-group-doubles-are-surjunctive
kind: claim
title: The Kun--Thom nonsofic group doubles over residually finite Kazhdan bases are surjunctive
distinct_from:
  kt-pair-group-double-is-nonsofic: that imports nonsoficity of these doubles from Kun--Thom Theorem A version 3; this proves they are surjunctive.
  kun-thom-nonsofic-wreaths-are-surjunctive: that treats the generalized wreath products of the same pairs; this treats the amalgamated doubles, through a free kernel instead of a lamp product.
artifacts:
  - research/artifacts/finitary-split-extension-surjunctivity-2026-09-11.md
---

Let `Gamma <= G` be a Kun--Thom pair with `G` residually finite, for example
the Theorem E pair

```text
Gamma = EL_r(F_q[x_1,...,x_d]),
G     = EL_r(F_q[x_1^(+-1),...,x_d^(+-1)]) semidirect SL_d(Z),     r,d >= 3.
```

Then the group double `G *_Gamma G` is surjunctive.

**Derivation.**
* `G` is residually finite, hence surjunctive.
* `doubles-of-surjunctive-groups-are-surjunctive` applies to every subgroup
  `Gamma`.

No sofic approximation is used.

By Kun--Thom Theorem A version 3, recorded in
`kt-pair-group-double-is-nonsofic`, these doubles are not sofic. So they give
a second family of surjunctive nonsofic groups, alongside
`kun-thom-nonsofic-wreaths-are-surjunctive`.
