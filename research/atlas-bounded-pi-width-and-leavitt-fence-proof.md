---
rg: 2
id: atlas-bounded-pi-width-and-leavitt-fence-proof
kind: route
title: Exhibit a PI-degree-one q14 family and evaluate universal identities in the Leavitt quotient
target: atlas-bounded-pi-width-and-leavitt-fence
requires:
  - atlas-square-root-frame-has-unit-packet-residual
  - atlas-augmented-relations-have-unbounded-chart-width
  - leavitt-unit-group-algebra-surjects-onto-leavitt
---

For the first assertion, use the regular module of
`B_h=F2[x,y]/(x^h,y^h)` and the chart change

```text
T_h=I+E13 tensor L_x+E14 tensor L_y.
```

The two off-diagonal summands have all pairwise products zero, so `T_h` is
an involution.  Both matrix units commute with `E23`, proving q14.  The
coefficient blocks recover `L_x,L_y`, hence their generated algebra is the
regular image of `B_h`.  This algebra is commutative, has dimension `h^2`,
and its radical `(x,y)` has nilpotency index `2h-1`.  The required packet
floor for this same triangular chart is the cited unit-packet claim.

For the second assertion, the established Leavitt chart image factors the
augmented Atlas group onto `Q=L_F2(1,2)^x`, and the cited unit-span theorem
then gives

```text
F2[Gamma_+] -> F2[Q] -> L_F2(1,2).
```

For binary words of length `r`, the elements `x_u y_v` are matrix units,
because `y_v x_p=delta_(v,p)`, and their diagonal sum is one.  Therefore
the last algebra contains `M_(2^r)(F2)` unitally for every `r`.  The free
associative algebra over `F2` is residually finite-dimensional (truncate its
left regular action beyond the maximum degree of a chosen nonzero
polynomial), so no nonzero free polynomial vanishes on all finite binary
matrix algebras.  The Leavitt algebra is consequently non-PI.  Polynomial
identities pass to quotients, proving that no bounded PI follows from the
augmented Atlas relations.
