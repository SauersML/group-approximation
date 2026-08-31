---
rg: 2
id: two-qutrit-active-atom-minimality-proof
kind: route
title: Compress the marked two-qutrit matrix block by its active rank-one atom
target: two-qutrit-and-atom-has-no-internal-joint-frame
requires:
  - two-qutrit-and-cell-retains-sectorwise-pauli-gauge
  - two-qutrit-controlled-bases-give-proper-multipath-marginal
---

The marked central character `J=omega` of the order-`3^5` extraspecial
group has its irreducible spin representation on a nine-dimensional space.
The proof of
`two-qutrit-controlled-bases-give-proper-multipath-marginal` identifies
the nine projections `p_(a,b)` as mutually orthogonal rank-one
projections summing to the marked central projection `q). Therefore

```text
q C[E]q isomorphicTo M_9(C),       rank(p_(a,b))=1.      (TAP1)
```

The intrinsic selector calculation gives `ST=p_(0,0)`, so `E_11` has
rank one. If `R` is a projection with `R<=E_11`, then
`Ran(R)<=Ran(E_11)`. The latter space is one-dimensional, hence
`rank(R)` is zero or one. In the nonzero case the ranges agree and
`R=E_11). This proves `(TAJ2)`.

For any rank-one projection `e` in a full matrix algebra,

```text
e M_n(C)e = C e.                                        (TAP2)
```

Indeed every compressed operator acts on the one-dimensional range of
`e`, so it is scalar there and zero off that range. Taking `e=E_11`
proves `(TAJ3)`. If a partial isometry `v` has nonzero source and range
under `E_11`, both support projections equal `E_11`, and `v` belongs
to the one-dimensional corner; thus `v=lambda E_11` with
`|lambda|=1`. If instead `vv^*<=p_(a,b)`, the same rank argument gives
`vv^*=p_(a,b)`. Its source and range both have rank one, so this is whole-
atom Murray--von Neumann transport, not a proper-corner occurrence.

Finally, for any finite-dimensional `D`, elementary tensor compression
gives

```text
(E_11 tensor 1)(M_9(C) tensor D)(E_11 tensor 1)
 =(E_11 M_9(C) E_11) tensor D
 =C E_11 tensor D.                                     (TAP3)
```

Under the canonical identification this is `D), and a projection in it
has the form `E_11 tensor r`. The compressed image of every selector-packet
operator `x tensor 1` is

```text
(E_11 x E_11) tensor 1=lambda_x E_11 tensor 1,          (TAP4)
```

so it cannot distinguish, conjugate, or jointly authenticate two operators
inside the external factor.

Equations `(TAP3)--(TAP4)` also show the exact scope of the theorem. They
do not rule out a larger ambient packet with mixed selector--reservoir
generators. They prove that such mixed generators are genuinely additional:
the two-qutrit finite group, its nine finite-type atoms, and their multipath
sums contain no positive proper corner or non-scalar common frame on which
to build the requested occurrence.
