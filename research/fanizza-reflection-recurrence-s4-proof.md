---
rg: 2
id: fanizza-reflection-recurrence-s4-proof
kind: route
title: Compute the stationary overlap in the affine two-bit group
target: fanizza-reflection-recurrence-has-s4-stationary-overlap
requires:
  - fanizza-doubling-carriers-form-orthogonal-flag
---

Write `V` additively as `F_2^2` with basis vectors denoted by `d,e`.
The matrices

```text
x=[[0,1],[1,0]],              u=[[1,0],[1,1]]
```

in the ordered basis `(d,e)` implement `(SFO1)` (columns are images of
basis vectors).  They are involutions.  Their action is transitive on the
three nonzero vectors, so together they generate `GL_2(F_2)`.  The affine
group therefore has order `4*6=24` and is the standard copy of `S_4`.

The first column of `u` gives `udu^(-1)=de`; the definition of `x` gives
`xdx^(-1)=e`, proving `(SFO3)`.

In the regular trace of a finite group, every nonidentity group element has
trace zero.  Since `d,e,de` are the three nonidentity elements of `V`,

```text
tau((1-d)/2)=tau((1-e)/2)=tau((1-de)/2)=1/2.
```

Moreover

```text
PR=(1-d-e+de)/4,
```

so `tau(PR)=1/4`.  The commuting-involution identity

```text
(1-de)/2=(1-d)/2+(1-e)/2-2(1-d)(1-e)/4
```

is `(SFO7)`.  Since `PR` is a projection,

```text
||2PR||_2^2=4 tau(PR)=1.
```

All statements survive amplification, completing the claimed exact finite
countermodel.
