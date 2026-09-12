---
rg: 2
id: leavitt-d4-length12-rank9-class-a-is-fenced-proof
kind: route
title: Eliminate both middle-equation branches in the balanced rank-nine (1,3,1) class
target: leavitt-d4-length12-rank9-class-a-is-fenced
requires:
  - leavitt-d4-length12-balanced-rank9-two-classes
---

Use the notation

```text
p=g1, u=g2, z=g3, v=g4, a=g7, b=g8,
c=g9, d=g10, e=g11.
```

The common middle carrier equation has the two exhaustive branches recorded
in `leavitt-d4-length12-balanced-rank9-two-classes`.

In branch I, `z=g5=1` and `g6=(uv)^-1`.  Free reduction gives

```text
H=c_0 d_1 (epa)_2 b_3,       A0=(pa)_3.
```

The first class-A equation is `H A0 H=1`.  Factor malnormality forces
`H` into copy 3, hence

```text
c=d=1, epa=1, pa=b^-2,
e=b^2, a=p^-1b^-2.
```

The third carrier equation is then

```text
b^-1_3 (ep)_0 = v^-1_0 b_3.
```

Its reduced normal forms give exactly two cases.  If `b=1`, then
`e=1`, `a=p^-1`, and `v=p^-1`; direct substitution in the boundary (A)
reduces it to `K=1`.  If `b` is nontrivial, then

```text
b^2=1, p=a=e=v=1,
K=b_3 b_0 b_3 b_1 u^-1_0 b_2 b_3 u_0.
```

The displayed reduced word contains nontrivial `b` syllables in copies 1,
2, and 3, so it cannot be a one-copy word for any value of `u`.

In branch II, `v=1`, `g5=z^-1`, and `g6=u^-1`.  Again

```text
H=c_0 d_1 (era)_2 b_3,       A0=(ra)_3.
```

The first equation `H A0 H z_3=1` forces `H` into copy 3.  The third
equation becomes `b^-1_3(er)_0=b_3`.  Consequently

```text
c=d=1, er=1, a=1, b^2=1, e=r^-1,
z=b r^-1 b.
```

Substitution in (A) gives

```text
K=b_3 b_0 (r^-1 b)_3 b_1 r_3 u^-1_0 b_2 b_3 u_0.
```

If `b=1`, this reduces to `K=1`.  If `b` is nontrivial, its copy-1 and
copy-2 `b` syllables are unavoidable, so it is not a one-copy word.  This
exhausts both branches and fences class A globally.

