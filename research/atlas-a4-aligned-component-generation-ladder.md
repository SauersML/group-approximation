---
rg: 2
id: atlas-a4-aligned-component-generation-ladder
kind: claim
title: The corrected A4 reference alignment turns the two packet components into the rank-three core and the full A8 chart
artifacts:
  - experiments/atlas_a4_reference_alignment.py
distinct_from:
  atlas-a4-packet-biclique-decomposition: that identifies the two raw label components as S3 and S3 x C3 and their K2,2/K2,4 incidence graphs; this computes what each raw component generates together with its correctly aligned conjugate.
  atlas-a4-19243-parabolic-subgroup-ladder: that starts from the collision S3 cell and adjoins specific chart elements to reach GL3, AGL3 and A8; this is an independent reference-alignment calculation attached directly to the thirty-context packet.
---

Let `R in A8 ~= GL4(F2)` be the fixed exact packet alignment

```text
00000001000100000100000000000100
```

from `atlas-a4-packet-centralizer-product-compiler`.  Let `H_6 ~= S3` and
`H_18 ~= S3 x C3` be the two raw packet-component subgroups from
`atlas-a4-packet-biclique-decomposition`.

Exact `F2` enumeration gives

```text
H_6 intersect R H_6 R^-1 = {1},
|<H_6, R H_6 R^-1>| = 168,                           (ALIGN-COMP-1)

H_18 intersect R H_18 R^-1 = {1},
|<H_18, R H_18 R^-1>| = 20160 = |A8|.                (ALIGN-COMP-2)
```

Thus the aligned small component closes exactly to the rank-three
`GL3(F2)` core, while the aligned large component already generates the whole
chart `A8` by itself.  In particular the central `C3` directions in the large
`K_(2,4)` biclique are not decorative: after the correct reference alignment
they are precisely what upgrades the local component from the rank-three core
to the full simple chart.

This sharpens the target for the holonomy compiler.  A dimension-free theorem
which turns the eight large-component A4 contexts into one coherent
intertwiner for `H_18` and `R H_18 R^-1` would already be a full-chart
commutant synchronization theorem; the small `K_(2,2)` component is then a
redundant rank-three calibration rather than the source of the missing chart
generation.
