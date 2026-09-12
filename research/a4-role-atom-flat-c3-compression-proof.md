---
rg: 2
id: a4-role-atom-flat-c3-compression-proof
kind: route
title: The C3 generator cycles the three nontrivial V4 characters
target: a4-role-atom-has-flat-c3-root-overlap
requires: []
---

Let `r_chi` denote the character projection in `C[V4]`.  The semidirect
product relation gives

```text
z^j r_chi z^(-j)=r_(chi o alpha^(-j)),                 (AMP1)
```

where `alpha` is the order-three automorphism of `V4`.  Its action on the
three nontrivial characters is free.  Hence, for `j=1,2`, orthogonality of
the `V4` character projections gives

```text
r_chi z^j r_chi=0.                                    (AMP2)
```

The three-dimensional block of `A4` restricts to the direct sum of those
three nontrivial characters, so `r_chi<=c_3`.  Equations `(AMR1)` and
`(AMP2)` now yield the group-algebra identity

```text
r_chi p_z r_chi=(1/3)r_chi.                           (AMP3)
```

If `Q` and `P` commute with `K`, then `E=QPr_chi` is a projection below
`r_chi`.  Compressing `(AMP3)` by `QP` proves the first identity in
`(AMR3)`.  Traciality gives

```text
tr(Ep_z)=tr(Ep_zE)=(1/3)tr(E),
```

and subtraction proves the second.

For a fixed approximate presentation, correct the finite `A4` packet and
average the finitely many prescribed carriers and payload projections over
it.  Fixed finite-group stability, finite Fourier expansion, and the
contractivity of conditional expectation change `(AMR3)` by
`O(sqrt(E_pres))`, with no dependence on matrix dimension.
