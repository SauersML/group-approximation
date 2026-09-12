---
rg: 2
id: leavitt-no-odd-nine-corner-relations
kind: claim
title: The six Leavitt corner labels have no cyclically reduced relation of length nine
artifacts:
  - research/artifacts/classify-leavitt-odd-five-seven-corners.py
  - research/artifacts/leavitt-odd-nine-and-long-face-partitions-2026-08-21.md
distinct_from:
  leavitt-no-odd-five-seven-corner-relations: that closes the multi-odd-face branch forced by curvature; this eliminates the first exceptional one-odd-internal-face length.
  leavitt-even-region-short-atlas-has-area-ten: that treats even internal regions via bipartite cubic cores; this is an actual odd-girth calculation in G_0*G_1.
---

There is no cyclically formally reduced length-nine word in

```text
h_0,h_2,k_0,k_1,h_1^(+-1),k_2^(+-1)
```

which becomes trivial in `G_0*G_1` under the three-gate substitutions.
Modulo cyclic rotation and inversion there are exactly `2241906`
representatives.  Exact bridge expansion, commuting-root simplification,
and moved-vector syllable certificates leave zero survivors.

Consequently the unique odd internal face of any surviving area-eight
kernel picture has length `11,13`, or `15`.

