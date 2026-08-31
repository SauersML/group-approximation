---
rg: 2
id: qutrit-first-mixed-cycle-cell-finite-proof
kind: route
title: Collect the mixed st cell and close its qutrit orbit in a finite triangular algebra
target: qutrit-first-mixed-cycle-cell-is-finite
requires:
  - qutrit-first-cycle-phase-flip-is-a-finite-amalgam
  - qutrit-first-nonparallel-cuntz-return-chain-is-finite
---

## The cross-row Cuntz return

Fix `a modulo four` and abbreviate

```text
u=c_(a+2),       v=c_a,       p=c_(a+1).
```

Then

```text
X(t)=x_(u,v)(t),             t in T=span{t_0,t_1},
Y(s)=x_(p,u)(s),             s in S=span{s_0,s_1}.
```

These root positions meet in the second Steinberg orientation. In
characteristic two,

```text
[X(t),Y(s)]=x_(p,v)(st)=Z(st).                           (QMX6)
```

The four products `s_rt_s` are linearly independent. Multiplying a
putative dependence on the left by `t_i` and on the right by `s_j`
extracts its `(i,j)` coefficient. Their span

```text
P_2=span{s_rt_s:r,s in {0,1}}
```

is the matrix-unit algebra `M_2(F_2)`, and

```text
s_0t_0+s_1t_1=1.                                        (QMX7)
```

Putting `t=t_r` and `s=s_r` in `(QMX6)` and multiplying the two
central return roots proves `(QMX2)`.

## Exact order of the cell

The only nontrivial commutators among the displayed root spaces are

```text
[X(t),Y(s)]=Z(st).
```

The `Z` roots commute with both `X` and `Y`. Ordered collection
therefore gives a normal form

```text
X(t)Y(s)Z(w),          t in T, s in S, w in P_2.         (QMX8)
```

As a three-by-three block this element has three off-diagonal entries.
They recover `t`, `s`, and then `w`, so the form is unique. Since the
three coefficient spaces have dimensions `2,2,4`,

```text
|N_a|=2^(2+2+4)=256.                                    (QMX9)
```

If an element of `N_a` has all coefficients in the scalar field, the
`T` and `S` entries first force `t=s=0`. The remaining matrix-unit
entry is scalar only for `w=0` or `w=1`. Consequently

```text
N_a intersect GL_28(F_2)=<Z(1)>=<D_(a+3)>.               (QMX10)
```

## Alternating qutrit types

The coordinate types around the actor cycle are

```text
type(c_0,c_1,c_2,c_3)=(triv,nontriv,nontriv,triv).
```

The root `X_(a,s)` joins opposite coordinates, hence always joins
different types and has the complete equal-`h` graph. The root
`Y_(a+1,r)` joins `c_(a+1)` to `c_(a+2)`. These types agree for even
`a` and differ for odd `a`. Finally `D_(a+3)` joins `c_(a+1)` to
`c_a`; these types differ for even `a` and agree for odd `a`.
The complete/diagonal norm calculation in the preceding phase-flip
proof now gives exactly `(QMX4)`.

## The qutrit closure is finite

It remains to check that the same-type commutation rows and the
different-type complete rows can be realized simultaneously, rather than
only as separate support tables.

Let `V_v,V_u,V_p` be the three distinct `C`-invariant coordinate
summands containing `v,u,p`. If two have the same `C` type, they are
the corresponding coordinates in distinct multiplicity copies; they
are still distinct invariant summands. Order them as

```text
V_v -> V_u -> V_p.
```

Let `mathcal n_C` be the `F_2`-span of all `C` conjugates of the
`X,Y,Z` root spaces and all their products. Conjugation by `C` acts
inside each of the three finite-dimensional coordinate summands. Hence
the coefficient spaces in the three possible off-diagonal blocks are
contained in finite sums of copies of `T,S,P_2`. In particular
`mathcal n_C` is finite dimensional over `F_2`.

Every element of `mathcal n_C` is strictly upper triangular for the
displayed three-block order. Therefore

```text
mathcal n_C^3=0,
```

and `1+mathcal n_C` is a finite algebra group. By construction `C`
normalizes it and `N_a subset 1+mathcal n_C`. Thus

```text
<C,N_a> subset (1+mathcal n_C) semidirect C,
```

which proves `(QMX5)`.

Take the left regular representation of this finite group. Its
restriction to `C` is a multiple of the regular representation, so the
nine character projections all have normalized rank `1/9`. The
intersection computation from the phase-flip proof gives squared block
norm `1/27` for every complete entry and `1/9` for every diagonal
entry. All commutators and the additive return `(QMX2)` hold literally.

The escape from finite triangular algebra therefore requires overlapping
mixed cells whose combined coordinate quiver contains a directed cycle.
One such cell, even though it already consumes both `s_r` and `t_s` and
the identity `s_0t_0+s_1t_1=1`, cannot carry the desired defect.
