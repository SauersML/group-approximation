---
rg: 2
id: rank-one-additive-swap-cycles-only-read-isotropy-holonomy
kind: claim
title: Rank-one additive swap cycles only read ordinary isotropy holonomy
distinct_from:
  d8-two-path-corner-cell-is-a-gauge-free-swap: that computes one edge and finds its removable gauge; this computes the first gauge-invariant parallel-edge and triangle cycles.
  finite-projective-sector-groupoids-have-conjugate-absorbers: that gives the abstract groupoid absorber; this identifies the lowest-degree corner polynomials and their underlying return words.
---

# Rank-one additive swap cycles only read ordinary isotropy holonomy

ESTABLISHED. The first gauge-invariant polynomial appears with two parallel
`D_8` cells. Use the projections `p_0,p_1` from
`d8-two-path-corner-cell-is-a-gauge-free-swap`, and let two stable letters
`t,u` both carry `p_0` to `p_1`. Put

```text
V_t=t p_0+t^(-1)p_1,       V_u=u p_0+u^(-1)p_1.          (RSC1)
```

Then the degree-two corner polynomial is

```text
p_0 V_u V_t p_0 = p_0 u^(-1)t p_0.                       (RSC2)
```

On multiplicity spaces it is exactly `U_u^*U_t`. Vertex gauges conjugate
this loop but cannot remove its spectrum. However, the right side of `(RSC2)`
is merely the compression of the ordinary return word `u^(-1)t`, which
stabilizes the rank-one packet type. The defining HNN relations impose no
condition on its multiplicity action, so every unitary can occur.

There is an equally explicit triangle. Let `K=A_4`, `H=V_4`, and let

```text
q=1-|H|^(-1)sum_(h in H)h
```

be the central projection of the three-dimensional irreducible type. Its
restriction to `H` splits as the three rank-one nontrivial character
projections

```text
q=p_0+p_1+p_2.                                           (RSC3)
```

For each edge `ij`, take a stable letter `t_ij` implementing the automorphism
of `H` which swaps characters `i,j` and fixes the third, and define

```text
V_ij=t_ij p_i+t_ij^(-1)p_j+p_k,       {i,j,k}={0,1,2}.   (RSC4)
```

Each `V_ij` is a self-adjoint corner involution. With the orientation
`0->1->2->0`,

```text
p_0 V_20 V_12 V_01 p_0
 =p_0 t_20 t_12 t_01 p_0,                                (RSC5)
```

whose multiplicity operator is the gauge-invariant loop
`U_20 U_12 U_01`. Thus degree three reads triangle holonomy, but again it is
only one ordinary isotropy return word.

There are two outcomes.

1. Leave the return word free. Then its multiplicity unitary is arbitrary,
   so the cell locks nothing.
2. Impose an ordinary compatible group relation equating the return word to
   its finite packet label. The corresponding stable edge is Tietze-redundant
   (the composite edge automorphism already agrees), so one merely removes a
   graph cycle and returns to finite graph-of-groups transport. No additive
   corner rigidity is created.

The formally useful relation would instead be only

```text
p_0 t_20 t_12 t_01 p_0=p_0                             (RSC6)
```

while leaving the full group word nontrivial off `p_0`. But `(RSC6)` is a
group-algebra corner equality, not an ordinary group relator. Expanding and
compiling it without killing the finite packet is precisely the signed-Hecke
term-pairing/relative-holonomy problem already isolated at the first chord.

Hence shared rank-one additive swaps successfully expose the relative gauge,
but ordinary group relations can only leave it arbitrary or collapse it as a
whole return word. The minimal viable next cell must overlap **transverse
noncommuting source partitions**, so its product expands into at least two
return words in the same corner and a relation can compare their sum rather
than kill one isotropy word.

