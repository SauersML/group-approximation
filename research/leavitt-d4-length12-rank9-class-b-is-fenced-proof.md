---
rg: 2
id: leavitt-d4-length12-rank9-class-b-is-fenced-proof
kind: route
title: Eliminate the unique copy-two syllable in both (2,2,1) branches
target: leavitt-d4-length12-rank9-class-b-is-fenced
requires:
  - leavitt-d4-length12-balanced-rank9-two-classes
---

Retain the notation of the class-A proof:

```text
p=g1, u=g2, z=g3, v=g4, a=g7, b=g8,
c=g9, d=g10, e=g11.
```

In common branch I, the first class-B equation is the same equation
`H A0 H=1` as in class A.  It therefore forces

```text
H=b_3, c=d=1, e=b^2, a=p^-1b^-2.
```

Put `f=ep`.  The third equation reduces exactly to

```text
b^-1_3 f_0
 = u^-1_0 f^-1_1 b_3 b^-1_2 f_1 (uv)_0 b_3.       (1)
```

If `b` is nontrivial, the right side contains the unique nontrivial
copy-2 syllable `b^-1_2`, whereas the left side contains no copy-2
syllable.  No free reduction can remove it, so (1) forces `b=1`.
Then `e=1`, `a=p^-1`, and (1) reduces in copy 0 to `p=v`.  Direct
substitution in boundary (B) gives

```text
K=p^-1_0 p_0=1.
```

In common branch II the first equation similarly forces

```text
H=b_3, c=d=1, era=1, z=b(ra)b=b e^-1 b.
```

The third equation is

```text
b^-1_3(er)_0
 =u^-1_0(er)^-1_1 b_3 b^-1_2 a^-1_1 u_0 b_3.      (2)
```

The same unique-copy-2 argument forces `b=1`.  Since `era=1`, one has
`a^-1=er`; the copy-1 terms and then the copy-0 terms on the right of
(2) cancel.  Thus `er=1`, whence

```text
a=1, e=r^-1, z=r.
```

Finally boundary (B) reduces to `K=e_3z_3=1`.  Both branches therefore
have trivial boundary.

