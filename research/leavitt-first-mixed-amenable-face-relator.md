---
rg: 2
id: leavitt-first-mixed-amenable-face-relator
kind: claim
title: A length-four Weyl transport is the first mixed kernel relation between the two amenable Leavitt faces
distinct_from:
  leavitt-one-compressor-defect-lies-in-amenable-subgroups: that proves each one-compressor face separately contains the manuscript defect and is amenable; this exhibits the shortest new relation created when the degree-zero and positive-parabolic base faces are joined.
  finite-positive-root-fragments-have-marked-regular-models: that gives finite models inside one positive-root face; this relation mixes a nonzero-degree positive root with a degree-zero opposite-root Weyl word.
  leavitt-diagonal-compression-is-elementary-amenable: that concerns the diagonal cylinder face and the marked root; this computes a kernel word between the full degree-zero core and the whole upper parabolic.
artifacts:
  - non_mf_groups_exist.tex
  - research/leavitt-one-compressor-defect-lies-in-amenable-subgroups.md
---

Put

```text
R_0 = union_k M_(2^k)(F_2),
L_0 = EL_3(R_0),
P   = U_3(R) semidirect T_0,
C_0 = L_0 cap P = U_3(R_0) semidirect T_0.
```

In `L_0`, let

```text
w=x_01(1)x_10(1)x_01(1),
```

the characteristic-two Weyl element interchanging coordinates `0` and `1`.
In `P`, put `u=x_02(s_0)` and `v=x_12(s_0)`. Then

```text
r = w u w^(-1) v^(-1)                                  (FMR1)
```

is nontrivial in the group amalgam

```text
A_0 = L_0 *_(C_0) P,                                   (FMR2)
```

but maps to the identity under the natural surjection `A_0 -> L=EL_3(R)`.
It has amalgam syllable length four, the smallest possible length of a new
reduced relation.

Thus `<L_0,P>=L` is already a proper quotient of two locally finite groups
amalgamated over their locally finite upper-triangular intersection. The
first obstruction is not a complicated compressor holonomy: it is the
nonzero-gauge Weyl transport `(FMR1)`.
