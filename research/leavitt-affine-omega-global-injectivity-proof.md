---
rg: 2
id: leavitt-affine-omega-global-injectivity-proof
kind: route
title: Nielsen-split the affine corners and eliminate the three feedback generators
target: leavitt-affine-omega-candidate-is-injective
requires:
  - leavitt-degree-four-affine-omega-candidate
  - leavitt-affine-omega-one-copy-picture-area-at-least-eight
---

Let `C=G_0*G_1*G_2*G_3`.  Cyclically reading the four orbit relators at
their stable-letter occurrences gives the short corners

```text
a=a_0,       e=e_0,       c=c_3,       q=q_3
```

and the long corners

```text
H=r_0|a_2|c_1|e_3|q_2|p_3,
K=a_1|c_0|e_2|q_1|p_2|r_3,
L=p_0|r_1|a_3|c_2,
N=e_1|q_0|p_1|r_2.                                  (AO1)
```

Exact faithful-Bergman calculation gives

```text
<a,e>=V4,                 <c,q>=D8.                  (AO2)
```

Indeed `a,e,c,q` are involutions, `a` commutes with `e`, and `cq` has order
four.  Put

```text
Q=V4(a,e)*D8(c,q)*F(H,K,L,N).                        (AO3)
```

The natural map `Q -> C` is injective.  Here is the Nielsen check.  A finite
gate syllable can meet a long endpoint only in copy zero or copy three.  The
only exposed units there are `r^+-1,p^+-1`, and none belongs to either finite
gate group.  For all noninverse pairs among
`H^+-1,K^+-1,L^+-1,N^+-1`, every same-copy endpoint product is nonidentity.
The artifact checks these statements exactly in the faithful Leavitt chart
(eight noninverse same-copy joins).  Consequently expansion of a reduced
`Q` word cannot start a cancellation cascade.  This proves `(AO3)` and also

```text
Q intersect G_0=V4(a_0,e_0),
Q intersect G_3=D8(c_3,q_3),
Q intersect G_1=Q intersect G_2=1.                  (AO4)
```

Over the abstract corner group, the four orbit relators are

```text
H z,
z e z^(-1) q z L,
z a z^(-1) c z N,
z K.                                                 (AO5)
```

They admit reversible Tietze elimination.  The first gives `z=H^(-1)`, the
last gives `K=H`, and the middle two give

```text
L=H q H^(-1)eH,          N=H c H^(-1)aH.             (AO6)
```

Each of `K,L,N` is a distinct free generator occurring on the left of one
equation.  Thus

```text
<Q,z | (AO5)> = (V4(a,e)*D8(c,q))*<H>,               (AO7)
```

and `Q` maps injectively on the finite-factor subgroup `V4*D8`.

Suppose a nonidentity `g in G_i` died in the full index-four quotient.  A
relative picture for `g` has every coefficient corner in `Q`.  Each inner
coefficient region is trivial in `C`; injectivity `(AO3)` makes it trivial
already in abstract `Q`.  On the outer region, `g` equals an element of `Q`.
By `(AO4)` it lies in the corresponding finite gate factor, or is already
trivial for `i=1,2`.  The same abstract picture puts that element in the
kernel of `Q -> (AO7)`, but `(AO7)` is injective on both finite factors.  This
is a contradiction.  Hence every `G_i` embeds in the index-four quotient.

Finally `W_8` has exponent sum four.  Mapping `t` to `1 in Z/4` and `G` to
zero identifies the index-four presentation above with the kernel, with the
original coefficient group equal to `G_0`.  Its injectivity proves the
claim.
