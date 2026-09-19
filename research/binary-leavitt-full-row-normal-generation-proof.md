---
rg: 2
id: binary-leavitt-full-row-normal-generation-proof
kind: route
title: Commute once transversely to isolate a nonzero coefficient root
target: binary-leavitt-full-row-elements-normally-generate
requires: []
---

Consider first a row element

```text
v=product_(ell!=i) x_iell(a_ell)!=1.
```

Some coefficient `a_j` is nonzero.  Choose `k` distinct from `i,j`, which
is possible already in rank three.  The same-row factors commute, and every
factor other than `x_ij(a_j)` commutes with `x_jk(1)`.  The Steinberg
commutator relation therefore gives, in characteristic two,

```text
[v,x_jk(1)]=x_ik(a_j).                                  (FRN2)
```

The left side belongs to the normal closure of `v`.  The right side is a
nonzero root element, so the machine-checked theorem

```text
BinaryLeavittSteinberg.normalClosure_root_eq_top
```

applies in rank at least five.  Hence the normal closure of `v` contains
the whole group, proving `(FRN1)`.

For a column element choose a nonzero coefficient `a_i` and an index `k`
distinct from the fixed column and from `i`.  The transposed calculation is

```text
[x_ki(1),v]=x_kj(a_i).                                  (FRN3)
```

Again the commutator lies in the normal closure of `v`, and the nonzero root
on the right normally generates `Delta`.  This proves the column statement
without any Property `(T)`, matrix-corona, rank, or character input.

