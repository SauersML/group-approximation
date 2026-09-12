---
rg: 2
id: degree-zero-leavitt-core-finite-model-proof
kind: route
title: Identify balanced prefix coefficients with nested finite matrix rings
target: degree-zero-leavitt-core-has-locally-finite-marked-models
requires:
  - returned-boolean-coefficient-window-has-finite-marked-model
  - atomic-leavitt-gap-on-nonzero-matrix-corner
---

For binary words of length `n`, the Leavitt cancellation rule is

```text
t_v s_a=delta_(v,a)1.
```

Therefore

```text
(s_u t_v)(s_a t_b)=delta_(v,a)s_u t_b.
```

Iterating `s_0t_0+s_1t_1=1` gives

```text
sum_(|u|=n)s_u t_u=1.
```

These are the full matrix-unit relations.  If

```text
sum_(u,v)c_(u,v)s_u t_v=0,
```

then multiplication by `t_a` on the left and `s_b` on the right yields
`c_(a,b)1=0`; hence every coefficient vanishes.  This proves the
isomorphism `(DLC3)`.

For `|u|=|v|=m<n`, insert the iterated range sum between `s_u` and `t_v`:

```text
s_u t_v
 =s_u (sum_(|w|=n-m)s_wt_w)t_v
 =sum_(|w|=n-m)s_(uw)t_(vw).
```

This proves `(DLC4)` and the nested union `(DLC5)`.  Every finite subset of
that union is contained in one `B_n`, which has exactly

```text
2^((2^n)^2)
```

elements.

For a finite coefficient inventory choose such an `n`.  All its elementary
root matrices, their inverses, arbitrary products and commutators, and all
constant root-index Weyl words lie in `E_20(B_n)`.  This is a finite group
because it is a subset of the finite set `M_20(B_n)`.  Every genuine word
identity from the literal Steinberg group remains an identity after the
canonical elementary quotient, so left translation supplies the claimed
simultaneous exact unitary model.

Finally,

```text
q_1=s_1t_1=sum_(|w|=n-1)s_(1w)t_(1w)
```

is nonzero by matrix-unit independence.  Hence `I+q_1E_13` is a
nonidentity involution in `E_20(B_n)`.  Left translation by it consists of
two-cycles, so its negative spectral projection is nonzero.  Repeating
this exact model at every input tolerance contradicts any alleged
vanishing-modulus Atomic Morita Return consequence by
`atomic-leavitt-gap-on-nonzero-matrix-corner`.
