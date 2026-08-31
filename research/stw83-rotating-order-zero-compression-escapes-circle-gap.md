---
rg: 2
id: stw83-rotating-order-zero-compression-escapes-circle-gap
kind: claim
title: A noncommuting compression of one order-zero colour can recover the circle generator
distinct_from:
  stw83-circle-unitary-order-zero-plus-constants-gap: that computes distance one for order-zero maps landing in the abelian rank-one corner; this shows the gap disappears after compressing an order-zero map whose range crosses the corner.
---

**ESTABLISHED.**  Let `z` be the coordinate unitary of `C(T)`.  For
every `epsilon>0` there are an integer `m>=2`, a unital star homomorphism

```text
pi:M_m -> M_m(C(T)),
```

a unitary `u in M_m`, and the constant rank-one projection
`e=e_(11) in M_m(C(T))` such that

```text
norm(e pi(u) e-z e)<epsilon.                             (1)
```

The compression

```text
kappa:M_m -> eM_m(C(T))e,
kappa(x)=e pi(x)e,
```

is ucp but is not order zero.  Thus the exact distance-one theorem
[[stw83-circle-unitary-order-zero-plus-constants-gap]] cannot be extended by
replacing an order-zero map into the plateau corner with the compression of
an arbitrary order-zero map into the full matrix-over-circle corner.

For the canonical circle-by-circle Toeplitz test, this proves that
coefficient variation on a plateau diagonal is compatible with a single
cross-boundary order-zero colour to arbitrary accuracy.  It does not prove
the relative two-colour approximation required by
[[stw83-plateau-buffer-recolouring-hinge]]: one must still approximate the
entire prescribed Toeplitz finite set while maintaining the two global
orthogonality pairings.  Conversely, a nuclear-dimension-two lower bound
cannot follow from rank-one diagonal compression alone; it needs rigidity
coupling that diagonal to the Toeplitz shift and to the other inputs.

DERIVATION
[[stw83-rotating-order-zero-compression-proof]]
