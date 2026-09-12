---
rg: 2
id: atlas-a4-19243-classical-collapse-proof
kind: route
title: Exhaust the two automorphism cosets after exact triangle filtering
target: atlas-a4-19243-classical-collapse
requires:
  - atlas-shortest-a4-triangle-packet
  - atlas-19243-s3-relative-normal-form
artifacts:
  - experiments/atlas_triangle_19243_packet.py
---

The replay enumerates `GL_4(F_2)` from the six standard transvections and
checks its order is `20160`.  For every alignment `h` it evaluates each free-
product relation exactly over `F_2` under

```text
factor 1: g -> g,
factor 2: g -> h g h^-1
```

and then repeats the scan with

```text
factor 2: g -> h (g^-1)^T h^-1.
```

These are the inner and outer automorphism cosets of `A8`.  Filtering first by
the thirty exact pair-cubes leaves exactly `30` alignments in each coset.  The
script then evaluates the stored eight-syllable word `q_19243` on those sixty
survivors.  The survivor counts are exactly

```text
                         triangle packet    + q_19243
inner                         30                 0
outer                         30                 0.
```

Every operation is multiplication/inversion/transposition of `4x4` matrices
over `F_2`; there is no numerical tolerance.  Since the two automorphism cosets
exhaust `Aut(A8)`, the asserted classical-sector exclusion follows.
