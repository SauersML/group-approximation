---
rg: 2
id: stw77-quotient-properness-does-not-lift-coordinatewise-proof
kind: route
title: Hide one rank-one coordinate packet in the product compact ideal
target: stw77-quotient-properness-does-not-lift-coordinatewise
requires:
  - oinfty-map-stability-is-central-isometry-splitting
---

Let `H` be a separable infinite-dimensional Hilbert space, set

```text
P=product_(n in N) B(H),
I=product_(n in N) K(H),
Q=P/I,
```

and let `q:P->Q` be the quotient map. The norm-bounded product `I` is a
closed two-sided ideal of `P`. Choose rank-one projections `p_n in B(H)`
and put `p=(p_n)_n in I`.

For `A=C direct_sum C`, define a unital homomorphism

```text
tilde_phi(a,b)=(a p_n+b(1-p_n))_n.
```

Since `q(p)=0`, the induced quotient map is

```text
phi(a,b)=q(tilde_phi(a,b))=b 1_Q.
```

The unit of `Q` is properly infinite: two fixed orthogonal isometries in
`B(H)`, viewed as constant sequences, remain orthogonal isometries after
applying `q`. Hence every nonzero positive element of the scalar range
`phi(A)=C1_Q` is properly infinite.

On the other hand, at every coordinate `n`,

```text
tilde_phi_n(1,0)=p_n
```

is a nonzero finite-rank projection and is not properly infinite in
`B(H)`. Thus none of the coordinate maps of this chosen lift satisfies the
bounded-operator pointwise-proper hypothesis.

Finally, `phi` is O-infinity-stable because its range is scalar and the two
constant-sequence isometries already commute with it. The construction
therefore isolates only the failed quotient-to-lift inference.
