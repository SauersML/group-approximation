---
rg: 2
id: stw22-half-slack-matrix-diffuse-s4-dichotomy-proof
kind: route
title: Put half-slack matrix values in codimension two and take the degree-four type moduli
target: stw22-half-slack-all-factor-weighted-copy-uniform-s4-fillings
requires:
  - stw22-matrix-weighted-copy-codimension-two-uniform-s4-fillings
  - stw22-diffuse-weighted-copy-uniform-s4-fillings
artifacts:
  - research/artifacts/stw22-dim5-factor-bundle-breakthrough-2026-08-31.md
---

In a diffuse II1 factor, (AF5-1) is strict slack, so the diffuse theorem
gives `epsilon_0^3/216000000` and global four-connectivity.

In `M_n`, put `r=rank(supp(a))`, `k=mr`, and `c=n-k`. The zero weight
gives a singleton. For a nonzero weight, `m>=2` and half slack imply

```text
2<=k<=n/2,       c>=n/2>=2.                           (AF5-3)
```

The matrix codimension-two theorem gives the larger modulus
`epsilon_0^3/276480` and global four-connectivity. Thus the diffuse number
works in both cases. Degreewise minima with the lower moduli give one
equi-`LC^4` family. The argument is pointwise and needs no continuous
factor-type stratum.