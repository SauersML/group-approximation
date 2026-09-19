---
rg: 2
id: binary-jacobson-joint-natural-completion-proof
kind: route
title: Let the braid choose its spectator and read the residual transverse swap
target: binary-jacobson-joint-shortest-cells-exclude-natural-completions
requires:
  - binary-jacobson-first-mixed-kernel-is-three-syllable
  - binary-jacobson-shortest-affine-braid-is-finite-marked
---

Write

```text
V=U directSum W,
U=<e_1,e_3>,              W=<e_2> directSum A.             (JJCP1)
```

The overlap `K~=GL_2(F_2)` acts naturally on `U` and trivially on `W`.
The natural two-dimensional `K`-module has no nonzero fixed vector or fixed
linear functional, and its endomorphism centralizer is `F_2`.  Therefore an
invertible map commuting with `K` preserves `(JJCP1)`, acts as the identity
on `U`, and is arbitrary on `W`.  In particular the image of the overlap
involution `h` fixes `e_1,e_3` and preserves `W`.

Put

```text
t=h(e_2) in W.                                               (JJCP2)
```

Both `h` and `s=(e_2 e_3)` are involutions.  The braid `(hs)^3=1` is
equivalent to

```text
h s h=s h s.                                                (JJCP3)
```

Apply `(JJCP3)` first to `e_3`.  The left side is `t`, while the right side
is `s(t)`.  Since `t in <e_2> directSum A` and `s` swaps `e_2,e_3` while
fixing `A`, equality forces

```text
t in A.                                                      (JJCP4)
```

Applying `(JJCP3)` to `e_2` now gives `h(t)=e_2`.  Hence `t!=0`, and the
four-space

```text
X=<e_1,e_2,e_3,t>                                           (JJCP5)
```

is invariant under `h,u,s,r`, with `h|_X=(e_2 t)`.  This proves `(JJC3)`.

It remains to evaluate the second cell.  On `X`, write the four basis labels
as `1,2,3,t`.  Then

```text
u=(1 2),             r=(1 2 3),             h=(2 t),
a_12=h u=(1 t 2),
a_23=r a_12 r^(-1)=(2 t 3),
a_31=r^2 a_12 r^(-2)=(3 t 1).                            (JJCP6)
```

Composition from right to left gives

```text
a_31 a_23 a_12=(1 t)(2 3).                                (JJCP7)
```

The prescribed controlled swap `c=(s,1)` acts in the head projection as
`(2 3)` and fixes every spectator.  Equations `(JJCP6)--(JJCP7)` therefore
leave the nonidentity factor `(1 t)`, contradicting `(JJC2)`.  Since no step
uses the dimension or the action of `h` on a complement of `<e_2,t>` in
`W`, the obstruction is uniform over all finite spectator dimensions.
