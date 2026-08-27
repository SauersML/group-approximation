---
rg: 2
id: leavitt-degree-four-target-picture-has-area-at-least-eight-proof
kind: route
title: Exhaust the 3,121,680 exact area-six mixed-valence ribbons
target: leavitt-degree-four-target-picture-has-area-at-least-eight
requires:
  - leavitt-degree-four-target-picture-has-area-at-least-six
  - leavitt-degree-four-one-copy-picture-has-area-at-least-eight
---

Use the exact signed-ribbon and faithful coefficient-normal-form enumerator in
`research/artifacts/search-leavitt-degree4-relative-pictures.py`.  At area six
there are `400` admissible multisets of the eight relator/orientation types.
Enumerating every opposite-sign stable-letter pairing, then imposing
connectedness and the spherical Euler equation, leaves exactly

```text
3,121,680
```

planar labelled ribbons.  For each ribbon, every complementary region is
reduced in

```text
G_0*G_1*G_2*G_3,
G_i=EL_20(L_(F_2)(1,2)),
```

using the exact twenty-leaf Bergman chart inside each factor.  Every possible
outer region is tested, both orientations of `[c_0,d_0]` are accepted, and
the reading may start at every coefficient-letter boundary.  The permitted
MSI run reports

```text
area=6 type_multisets=400 planar=3121680 exact_target_disks=0
```

Together with the complete area-two/four census and odd-area sign obstruction
in `leavitt-degree-four-target-picture-has-area-at-least-six`, this proves the
area-eight lower bound.
