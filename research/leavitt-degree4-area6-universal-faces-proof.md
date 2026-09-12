---
rg: 2
id: leavitt-degree4-area6-universal-faces-proof
kind: route
title: Reduce every exact area-six face again in the weaker universal packet group
target: leavitt-degree4-area6-faces-are-universal
requires:
  - leavitt-degree-four-corner-subgroup-is-v4-d8-f4
  - leavitt-degree-four-one-copy-picture-has-area-at-least-eight
---

The exact ribbon enumerator marks each stable-letter occurrence by its position
in its Reidemeister--Schreier relator.  Joining equal positions on oppositely
oriented copies of the same relator is an immediate picture dipole and is
discarded.

For every remaining planar area-six ribbon, each coefficient region is first
evaluated in the faithful Bergman chart.  Every exact identity is then reduced
independently in the weaker free product of four groups

```text
V4(a,b)*C2(c)*C2(d)*C2(e)*Z(p)*Z(r).                 (UF1)
```

The eight MSI shards report `nonuniversal_trivial_face_labels=0`.  Taking the
union of canonical cyclic labels across the shards gives

```text
(2,2): 4,  (4,4): 6,  (6,14): 10,
(8,16):16, (10,26):8, (14,38):4,                    (UF2)
```

for 48 labels total.  Thus every exact short identity face is explained by
involution cancellation, the source `V4` law, and free cancellation.  The
arbitrary-length reason is the corner Nielsen embedding proved in
`leavitt-degree-four-corner-subgroup-is-v4-d8-f4`; `(UF2)` is its independent
bounded audit and supplies the precise corridor carriers visible at area six.
