---
rg: 2
id: balanced-overlay-local-alternating-projection-proof
kind: route
title: Combine fixed-face curvature with the complete-overlay Friedrichs angle
target: balanced-overlay-local-alternating-projections-contract
requires:
  - quadratic-overlay-has-uniform-linearized-synchronization-gap
---

Work first in the operator ball of radius less than `1/2` around an exact
point `z`.  Projection ranks cannot change in this ball.  Each bounded binary
face variety is therefore one fixed-rank unitary orbit of at most `2^q`
joint spectral projections, where the face width `q` is fixed.  Spectral
functional calculus gives its metric projection the uniform expansion

```text
Pi_A(z+xi)=z+P_A xi+R_A(xi),
||R_A(xi)||_2 <= K ||xi||_op ||xi||_2.                    (LAP3)
```

The product over faces has the same constant because the norms are averaged
over disjoint occurrence blocks.  Equality-cloud projection is averaging
followed by spectral-sign rounding.  Expander averaging is an operator-norm
contraction and sign rounding has a fixed spectral gap near a reflection,
so uniformly

```text
Pi_B(z+xi)=z+P_B xi+R_B(xi),
||R_B(xi)||_2 <= K' ||xi||_op ||xi||_2.                   (LAP4)
```

Here `P_A,P_B` are the Hilbert--Schmidt orthogonal tangent projections.
The derivative of the face and equality residual map is, up to fixed
bounded comparison constants, the pair of normal projections
`(I-P_A,I-P_B)`.  The established complete-overlay Jacobian gap `(QLS1)`
therefore gives a uniform Friedrichs-angle estimate on the orthogonal
complement of `T_z Z_L=T_z A_L cap T_z B_L`:

```text
||P_B P_A xi||_2 <= rho_0 ||xi||_2,   rho_0<1.            (LAP5)
```

The estimate is uniform across character multiplicities because `(QLS1)`
was proved blockwise and the face/equality comparison constants depend only
on bounded width, bounded occurrence, and the equality-expander gap.

Choose `r` so that the two remainder constants in `(LAP3)--(LAP4)` contribute
less than `(1-rho_0)/3`.  Projecting along the smooth intersection stratum
absorbs the common tangent component into a nearby point of `Z_L`; rank
strata outside the chosen one remain operator distance at least one away.
Equations `(LAP3)--(LAP5)` then give `(LAP1)` with
`rho<1`.  Summing the geometric displacement series gives `(LAP2)` and
convergence to an exact point.  The identical argument with `A` and `B`
interchanged proves the reversed-order statement.

