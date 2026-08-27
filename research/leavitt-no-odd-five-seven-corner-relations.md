---
rg: 2
id: leavitt-no-odd-five-seven-corner-relations
kind: claim
title: The six Leavitt corner labels have no cyclically reduced relations of length five or seven
artifacts:
  - research/artifacts/classify-leavitt-odd-five-seven-corners.py
  - research/artifacts/leavitt-odd-five-seven-classification-2026-08-21.md
distinct_from:
  leavitt-area-eight-parity-breaking-dichotomy: that identifies length five and seven as the mandatory short targets whenever two internal faces are odd; this eliminates both targets exactly.
  leavitt-short-atlas-does-not-close-six-cells: that treats the even length-four boundary left by six relator vertices; this proves an odd-girth statement in the actual coefficient free product.
---

In the oriented alphabet

```text
h_0,h_2,k_0,k_1,h_1^(+-1),k_2^(+-1)
```

there is no cyclically formally reduced word of length five or seven that is
the identity after the substitutions

```text
h_0=a_0, h_2=e_0, h_1=q_0p_1,
k_0=a_1, k_1=q_1, k_2=p_0e_1
```

in `G_0*G_1`.

Modulo cyclic rotation and inversion there are `1682` length-five and
`58826` length-seven words.  Exact free-factor expansion, commuting-root
reduction, and moved-vector certificates eliminate every one.

Consequently an eight-cell kernel picture cannot have two or more odd
internal regions: `leavitt-area-eight-parity-breaking-dichotomy` would force
one of length five or seven.  Any surviving area-eight picture has exactly
one odd internal region, an odd outer region, and internal odd length in

```text
{9,11,13,15}.                                             (O57)
```

