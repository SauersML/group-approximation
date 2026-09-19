---
rg: 2
id: damped-adjoint-step-bypasses-code-riesz-at-exact-base
kind: claim
title: A damped Jacobian-adjoint step bypasses the code Riesz inverse at an exact base
distinct_from:
  complete-overlay-row-newton-is-a-code-riesz-multiplier: that identifies the completely bounded cost of an exact pseudoinverse; this uses no pseudoinverse and obtains a fixed residual contraction from one bounded adjoint step.
  quadratic-overlay-has-uniform-linearized-synchronization-gap: that proves the Hilbert--Schmidt spectral gap; this combines that gap with normalized incidence bounds to obtain a row-column-safe iterative solver.
  code-laplacian-has-uniform-cp-green-approximants: that approximates one scalar Laplacian inverse by a long Green polynomial; this needs only the degree-one polynomial supplied by a damped normal-equation step.
---

ESTABLISHED LINEAR BYPASS.  Let `D:H->K` be the Jacobian at an exact
balanced-overlay code tuple, with the normalized domain and residual
Hilbert--Schmidt norms.  The complete-pair calculation and the bounded
sparse incidence layers give constants independent of code length and
matrix dimension such that

```text
 ||D||_(2->2)<=M,
 ||Dh||_2^2>=kappa||h||_2^2       (h perpendicular ker D).       (DAS1)
```

Use the quotient by `ker D`, which is the simultaneous-conjugation tangent,
and choose `0<eta<=M^(-2)`.  The damped normal-equation step

```text
 h |-> h-eta D*Dh                                                   (DAS2)
```

has spectrum `1-eta lambda` for
`lambda in [kappa,M^2]`.  Therefore

```text
 ||h-eta D*Dh||_2 <=(1-eta kappa)||h||_2.                           (DAS3)
```

Equivalently, on compatible residuals `r=Dh`, the correction
`-eta D*r` contracts the residual by the same fixed factor.  No division by
the character-dependent weight `|supp(chi+psi)|` occurs.

This step is safe in normalized operator row and column norms.  Every
bounded-width/bounded-degree derivative is a fixed sum of left and right
unitary multiplications.  For the dense pair layer, `D*` is a normalized
average over the second coordinate.  Operator Jensen gives, schematically,

```text
 (1/L)sum_i |(1/L)sum_j u_ij b_ij v_ij|^2
       <=(1/L^2)sum_(i,j)|b_ij|^2,                                  (DAS4)
```

and the adjoint inequality gives the row version.  Splitting the two terms
of each commutator derivative changes only an absolute constant.  Hence
both `D` and `D*` have dimension-independent row and column amplification
bounds.  The correction in `(DAS2)` costs at most `eta C_D` times the
residual square-function norm.

Thus `(CRM3)`, a uniform cb bound for the assembled code-Riesz
**pseudoinverse**, is not a necessary exact-base input.  Fixed-factor
Landweber iteration uses a bounded polynomial step and the already proved
`L_2` gap.  The remaining issue is nonlinear and off-base: prove directly
that the Jacobian-adjoint update evaluated on a diffuse contraction tuple
decreases the full balanced residual up to the established cb-quadratic
remainder, without first choosing a nearby exact character decomposition.

