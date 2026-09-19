---
rg: 2
id: deligne-central-mark-collapse-via-maslov-sector
kind: route
title: Eliminate the two nontrivial central spectral sectors
target: deligne-central-mark-hs-collapse
requires:
  - deligne-triple-cover-fd-central-invisibility
  - finite-central-hs-sector-decomposition
  - maslov-mod3-projective-defect-gap
artifacts:
  - research/artifacts/deligne-maslov-hyperlinear-strategies-2026-08-21.md
---

Apply `finite-central-hs-sector-decomposition` to an almost representation of
`E_3`.  After `o(1)` change the central unitary is

```text
Z=P_0+omega P_1+omega^2 P_2.                             (DCS1)
```

If either `P_1` or `P_2` had dimension proportion bounded below along a
subsequence, the weighted projective defects on that block would tend to zero,
contradicting `maslov-mod3-projective-defect-gap`.  Therefore

```text
tr(P_1)+tr(P_2)->0.
```

Equation `(DCS1)` then gives `||Z-I||_2->0`, and undoing the `o(1)` spectral
rounding proves `deligne-central-mark-hs-collapse`.

`deligne-triple-cover-fd-central-invisibility` is not logically needed after
the projective gap is granted, but records why the two exact projective target
varieties are empty and is therefore kept as an explicit dependency of the
research route.
