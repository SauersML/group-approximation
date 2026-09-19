---
rg: 2
id: qutrit-any-finite-router-polar-carries-at-most-half-residual
kind: claim
title: Every finite-head qutrit router polar carries at most half the selected residual
artifacts:
  - research/qutrit-finite-router-polar-capacity-proof.md
distinct_from:
  qutrit-external-cyclic-router-selects-only-one-hidden-third: that computes one minimal router and its one-third carrier; this gives the sharp universal one-half ceiling for arbitrary multi-router interference inside any finite overgroup.
  qutrit-same-double-coset-interference-cannot-expand-carrier: that treats sums within one double coset by scalar Fourier diagonalization; this allows distinct double cosets and arbitrary finite analytic linear combinations.
  finite-overgroup-packing-preserves-hyperlinearity: that proves a qualitative permanence theorem; this computes the exact D8-coupled trace capacity which blocks the desired full carrier.
---

Let `E=<j,z,w> isomorphic to C_3^3` lie in the qutrit packet, let
`R=p_0+p_1` and let `p_2=q-R`. Let `B` be any finite overgroup
of `E`. For any analytic finite-head router `X in C[B]` satisfying

```text
X=p_2 X R,
```

let `W` be its polar partial isometry and `P=W^*W`. Then

```text
P<=R,        WW^*<=p_2,        tau(P)<=tau(p_2)=1/9.   (QFC1)
```

This includes every two-router or multi-router linear combination whose
phase graph has only the complementary target.

Attach `B` to the Jacobson/D8 base along `E`, and let `V_eta` be either
exact D8 polar branch. The canonical amalgam trace satisfies

```text
||W V_eta||_2^2=tau(P)/32<=1/288.                       (QFC2)
```

But

```text
||R V_eta||_2^2=1/144.
```

Hence the polar of any finite-head interference operator carries at most
one half of the selected residual mass. The minimal cyclic router carries
one third; adding distinct double cosets can improve that number only up to
one half, never to a full-source carrier.

The bound is independent of the number of finite router words and of their
complex coefficients. Therefore no analytic compression confined to a
finite overgroup, even after coupling to the raw D8 residual, can supply the
missing two-to-one polar. A surviving construction must put the interfering
words in an infinite vertex and impose a joint relation not factored through
the finite edge algebra `C[E]`.
