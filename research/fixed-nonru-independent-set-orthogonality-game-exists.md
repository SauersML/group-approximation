---
rg: 2
id: fixed-nonru-independent-set-orthogonality-game-exists
kind: claim
title: A fixed independent-set game has perfect commuting value and a finite-dimensional overlap gap
artifacts:
  - research/artifacts/independent-set-rounding-rank-router-2026-08-23.md
distinct_from:
  oracularizable-tracial-nonru-game-exists: that supplies the original constraint-variable predicate game; this replaces its entire rejection predicate by pairwise projection orthogonality.
---

**ESTABLISHED.**  There is a fixed finite independent-set game `I_0` with

```text
omega_co(I_0)=1,
omega_qa(I_0)<=1-delta_0                              (NIS1)
```

for one `delta_0>0`, and with a perfect commuting strategy represented by a
single tracial family of row PVMs.  Its finite-dimensional loss is exactly a
fixed rational weighted sum

```text
L_I=sum_f alpha_f||P_fQ_f||_2^2,                      (NIS2)
```

over forbidden answer pairs.  Hence every finite-dimensional row-PVM family
obeys `L_I>=delta_0`, whereas the perfect commuting family makes every
overlap in `(NIS2)` zero.

