---
rg: 2
id: one-root-mixed-braid-native-target-proof
kind: route
title: Test the first Hecke fixed-space term after one root and the native Whitehead
target: one-elementary-root-cannot-return-mixed-braid-native-chart
requires:
  - one-elementary-root-cannot-return-mixed-braid-chart
  - two-distinct-reverse-hecke-roots-cannot-return
---

Use the actor basis `(2,4,5,6,7,8,9)`.  The intrinsic filtration from
`two-distinct-reverse-hecke-roots-cannot-return` begins with

```text
F_1=<e_2,e_7>_R,
```

and every element normalizing `L_0` preserves `F_1` after scalar extension
to the binary Leavitt algebra `R`.

The `(7,9)` block `(ORN1)` gives

```text
P e_7=q_0e_7+q_1e_9.                                  (1)
```

The `(7,8)` block `(ORN2)` gives

```text
J e_7=(1-q_0)e_7+x_1e_8,       J e_9=e_9.             (2)
```

Using `(1-q_0)q_0=0` and

```text
x_1q_0=(s_00t_0)(s_0t_0)=s_00t_0=x_1,
```

equations `(1)--(2)` yield `(ORN6)`.

Now let `R_0=1+cE_ab`, `a!=b`.  On an arbitrary column vector `v`, this
root changes only coordinate `a`, by adding `c v_b`.  Applied to `(1)`, it
does nothing unless `b` is `7` or `9`, and in either case it adds one term
supported on the single coordinate `a`:

```text
R_0Pe_7=Pe_7+d e_a,
d=cq_0  if b=7,       d=cq_1 if b=9.                 (3)
```

The Whitehead `J` fixes every coordinate outside `{7,8}` and only mixes
coordinates `7,8`.  Hence:

* if `a` is outside `{7,8,9}`, equation `(3)` changes neither the `e_8`
  nor the `e_9` term of `(ORN6)` (for `a=2` the correction lies in `F_1`;
  for every other such `a` it also adds a new component outside `F_1`);
* if `a` is `7` or `8`, it can change the `e_8` component but leaves the
  coefficient `q_1` of `e_9` unchanged;
* if `a=9`, it can change the `e_9` component but leaves the coefficient
  `x_1` of `e_8` unchanged.

The case `b` outside `{7,9}` is just `(ORN6)`.  Since the reduced Leavitt
matrix units `x_1=s_00t_0` and `q_1=s_1t_1` are nonzero, every case leaves
an `e_8` or `e_9` component.  Neither coordinate belongs to `F_1`, proving
`(ORN7)`.

If `J^(-1)R_0P` normalized `L_0`, it would equal `JR_0P` because `J^2=1`
and would preserve `F_1`, contrary to `(ORN7)`.  This proves `(ORN4)`.
Finally equality in `(ORN5)` would imply

```text
(J^(-1)R_0P)Q(J^(-1)R_0P)^(-1)=Q.
```

Equality of the two finite Reynolds sums forces equality of their group
supports and hence normalization of `L_0`, contradicting `(ORN4)`.
