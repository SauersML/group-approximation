---
rg: 2
id: d8-two-path-corner-cell-is-a-gauge-free-swap
kind: claim
title: The smallest D8 two-path corner cell is an exact but gauge-free swap
distinct_from:
  finite-projective-sector-groupoids-have-conjugate-absorbers: that gives the general finite-groupoid absorber; this constructs and computes the smallest explicit additive two-path block.
  single-group-word-compression-unitary-normalizes-corner: that excludes one compressed word; this uses the minimal sum of two stable-letter paths.
---

# The smallest D8 two-path corner cell is an exact but gauge-free swap

ESTABLISHED. Write

```text
D_8=<r,s | r^4=s^2=1, srs=r^(-1)>,       z=r^2,
H=<z,s> isomorphic to C_2 x C_2.
```

The two-dimensional irreducible type of `D_8` has central projection

```text
q=(1-z)/2.
```

Inside `qC[D_8]q=M_2(C)` take the two rank-one projections

```text
p_0=(1-z)(1+s)/4,       p_1=(1-z)(1-s)/4,       p_0+p_1=q. (DTP1)
```

Let `phi in Aut(H)` be

```text
phi(z)=s,       phi(s)=zs,
```

and form the HNN extension with stable letter `t` satisfying
`t h t^(-1)=phi(h)`. Direct substitution gives

```text
t p_0 t^(-1)=p_1.                                       (DTP2)
```

Therefore the two-path algebraic corner element

```text
V=t p_0+t^(-1)p_1                                       (DTP3)
```

satisfies

```text
V^*=V,       V^2=q.                                     (DTP4)
```

It is genuinely outside the single-word case: `t` cycles the three
nontrivial characters of `H` and does not stabilize `q`.

Nevertheless `(DTP3)` locks no multiplicity holonomy. In any unitary
representation, write `H_i=p_i H`. Relation `(DTP2)` gives a unitary
`U:H_0->H_1`, and on `H_0 direct_sum H_1`,

```text
V = [ 0   U^* ]
    [ U    0  ].                                        (DTP5)
```

Conjugation by `diag(I,U^*)` turns `(DTP5)` into the fixed scalar swap
`[[0,I],[I,0]]`. Thus the entire multiplicity unitary is gauge. The HNN
relations leave the three-step return `t^3` as arbitrary isotropy holonomy;
the two-path involution neither sees nor constrains it.

This is the smallest higher-dimensional finite packet (`|D_8|=8`) and the
minimal two-piece corner involution. It proves that additive multi-path
support is necessary but not sufficient. A viable signed-Hecke chord needs
at least two additive cells sharing blocks in a way that makes their gauge
loop observable, or a polynomial relation involving a nontrivial overlap of
their source/range partitions. One isolated rank-one two-path cell is only a
matrix swap.

