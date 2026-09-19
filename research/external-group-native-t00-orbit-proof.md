---
rg: 2
id: external-group-native-t00-orbit-proof
kind: route
title: Traverse the exact t00 endpoint orbits in the external-return group
target: external-group-misses-native-t00-roots
requires:
  - minimal-t00-conversion-cannot-return-native-whitehead-root
  - external-return-group-has-only-spectator-singer-centralizers
  - fused-cross-returns-cancel-positive-l0-gauge
---

Represent constant actor matrices by seven binary bit rows.  Close the ten
`L_0` generators to `8192` matrices, verify that each of the eight external
roots normalizes that set, and enumerate `256` right cosets.  This
independently checks the group size in `(XTR1)` before the orbit audit.

Conjugacy of a coefficient root by a constant matrix depends only on its
rank-one matrix position.  Starting from each of the ten transvections in
`(XTR2)`, breadth-first traverse conjugation by the eighteen involutory
generators.  Store each distinct matrix state once; this explores the exact
`G_X` orbit without enumerating `2097152` group words separately for every
case.  Compare every state with the appropriate native target
transvection.  The orbit sizes are exactly `(XTR4)`, and all ten target
membership tests are false.

Because the external generators include all adjacent arrows in the
topological order `(6,9,5,8,4,7,2)`, they generate the full unitriangular
group in `(XTR1)`.  Therefore orbit closure under those generators proves
the all-word assertions `(XTR3)`, not merely a bounded-length search.
