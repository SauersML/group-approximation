---
rg: 2
id: damped-cloud-averaging-contracts-from-exact-faces
kind: claim
title: Damped cloud averaging strictly contracts sparse energy from the exact-face sheet
distinct_from:
  balanced-overlay-local-alternating-projections-contract: that proves geometric convergence in an operator-norm tube by nonlinear metric projections; this gives one global contraction step from any exact local-face tuple using only affine contraction interpolation.
  fixed-parity-faces-exactify-with-loewner-row-square-control: that moves an arbitrary tuple onto the exact-face sheet with bounded cost; this moves off that sheet toward equality and proves a strict energy gain.
  normalized-occurrence-equality-transfer-preserves-face-gap: that transfers an averaged adjoint channel gap; this directly decreases the defining sparse residual energy.
---

ESTABLISHED ONE-SIDED DESCENT.  Let `(A_(i,v))` be occurrence reflections
whose every bounded face is exact: within each face they commute and obey
the prescribed parity product.  In equality cloud `i`, let
`lambda_(i,v)` be the stationary occurrence law and put

```text
 S_i=sum_v lambda_(i,v)A_(i,v),
 X_(i,v)(t)=(1-t)A_(i,v)+tS_i,       0<=t<=1.          (DCA1)
```

The `(X_(i,v)(t))` are selfadjoint contractions.  If `E_eq` is the
normalized squared equality-edge energy and `E_face(t)` is the normalized
sum of their involution, within-face commutator, and parity-word squared
residuals, then

```text
 E_eq(t)=(1-t)^2 E_eq(0),
 E_face(t)<=C_0 t^2 E_eq(0),                           (DCA2)
```

where `C_0` depends only on face width, balanced occurrence constants, and
the equality-expander gap.  Consequently, for

```text
 t_0=1/(1+C_0),       rho_0=C_0/(1+C_0)<1,
```

one has

```text
 E_eq(t_0)+E_face(t_0)<=rho_0 E_eq(0).                 (DCA3)
```

The movement is local in normalized Hilbert--Schmidt metric:

```text
 avg_(i,v)||X_(i,v)(t_0)-A_(i,v)||_2^2
 <=t_0^2 lambda_eq^(-1)E_eq(0).                        (DCA4)
```

Thus the equality-dominated branch of the joint-descent gate has a genuine
strict step whenever the tuple is on the exact-face sheet.  No character
decomposition, operator-norm tube, or individual occurrence bound is used.

This does not yet establish
`parity-charge-or-green-divergence-has-strict-descent`.  After `(DCA3)` the
faces are only approximately exact.  Applying the available full Loewner
face exactification has bounded cost, but no proved sign on its first-order
change of equality energy.  The remaining gate is a return map to the
exact-face sheet whose equality increase is strictly smaller than the gain
in `(DCA3)`, or a two-step Lyapunov cross term proving the same fact.

The standard local return is now ruled out sharply.
`damped-cloud-face-return-has-an-exact-scalar-fixed-sheet` shows that on
every inconsistent scalar exact-face tuple, damping by `t<1/2` preserves all
occurrence signs and the explicit sign-first Loewner exactifier returns the
old tuple verbatim.  Its positive equality cross term is exactly the missing
`2t(1-t)E_eq`, so together with the quadratic return term it cancels all of
the gain in `(DCA2)`.  A successful return must therefore coordinate its
face-character choices globally; improving only the local correction
constant cannot prove strict descent.
