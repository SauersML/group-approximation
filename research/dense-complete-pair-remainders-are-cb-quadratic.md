---
rg: 2
id: dense-complete-pair-remainders-are-cb-quadratic
kind: claim
title: Dense complete-pair Newton remainders are quadratically small in operator row-column norm
distinct_from:
  normalized-hs-taylor-remainder-is-not-dimension-free: that treats arbitrary coordinatewise HS perturbations and shows sparse high-operator-norm products can remain linear; this uses the dense normalized pair average and the common row-column square function to recover a genuine quadratic estimate
  balanced-overlay-diffuse-square-function-newton: that must combine dense-pair Newton with bounded parity faces and equality clouds; this settles the nonlinear remainder only for the dense complete-pair layer
---

For matrices `X_1,...,X_L`, put

```text
 H_c=(1/L)sum_i X_i^*X_i,
 H_r=(1/L)sum_i X_iX_i^* .                               (DQR1)
```

The normalized family of all quadratic products has the exact estimates

```text
 (1/L^2)sum_(i,j)(X_iX_j)^*(X_iX_j)
    <= ||H_c||_op H_c,

 (1/L^2)sum_(i,j)(X_iX_j)(X_iX_j)^*
    <= ||H_r||_op H_r.                                   (DQR2)
```

Consequently its operator column and row norms are at most, respectively,
`||H_c||_op` and `||H_r||_op`.  If the coordinate correction has row-column
norm at most `eta`, the complete-pair quadratic Taylor remainder has
row-column norm at most `eta^2`, with no dependence on `L` or matrix
dimension.

For the first inequality,

```text
 (1/L^2)sum_(i,j) X_j^*X_i^*X_iX_j
   =(1/L)sum_j X_j^* H_c X_j
   <=||H_c||_op H_c.                                    (DQR3)
```

The second is the adjoint calculation.  Higher fixed-degree dense terms are
handled by iterating the same estimate.

This removes the generic normalized-HS Taylor obstruction on the dense
complete-pair layer after the common square-function cut.  It does not
control the bounded parity and equality templates: their sparse incidence
averages can concentrate on individual coordinate outliers and do not equal
a full product average.  The remaining diffuse-basin theorem must alternate
uniform exact local face projections/geodesic equality alignment with this
dense cb-quadratic step, while proving that the global row gap survives the
alternation.
