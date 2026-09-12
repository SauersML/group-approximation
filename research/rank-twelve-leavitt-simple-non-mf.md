---
rg: 2
id: rank-twelve-leavitt-simple-non-mf
kind: claim
title: The rank-twelve binary-Leavitt elementary group is simple, Kazhdan, and non-MF
root: true
artifacts:
  - research/rank-twelve-leavitt-simple-non-mf-proof.md
  - non_mf_groups_exist.tex
---

Let `R=L_(F_2)(1,2)` and

```text
H=EL_12(R).
```

Then `H` is nontrivial, finitely generated, simple, has property `(T)`, and

```text
Rad_MF(H)=H.
```

Equivalently, every homomorphism from `H` to an MF group is trivial.  Every
finite-dimensional linear representation of `H` over every field is also
trivial.

The rank twelve is obtained from a rank-three Kazhdan source and four
rank-three Whitehead blocks.  Simplicity replaces the separate root-spreading
calculation: once the explicit compression defect `e_02(s_1*t_1)` is shown
nonzero, it automatically normally generates `H`.
