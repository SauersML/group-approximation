---
rg: 2
id: tight-defect-column-solves-algebraic-projection-crt
kind: claim
title: A scaled partial-isometry defect column solves the projection CRT algebraically
distinct_from:
  shared-involution-right-ideal-interpolation-criterion: that characterizes all Hilbert-space solutions and leaves a support projection in the von Neumann closure; this gives a finite polynomial certificate forcing that support projection to lie in the original star algebra.
  fano-cap-sequential-products-form-an-algebraic-naimark-carrier: that stacks a complete cap menu into an external matrix projection; this constructs the actual internal interpolation projection from the sum-and-difference defect column.
  universal-residual-wordization-collapses-carrier: that forbids universal lower bounds converting residual mass into defining-word energy; this is an exact algebraic interpolation identity and asserts no such energy inequality.
---

**ESTABLISHED.**  Let `R` be a unital star-subalgebra of a finite von
Neumann algebra.  With the notation `(SIC1)`, assume the compatibility
equations

```text
X^*X=Y^*Y,                    X^*Y=Y^*X.               (TDC1)
```

Put

```text
D=X-Y:R^r -> R.                                      (TDC2)
```

If there is a scalar `lambda>0` such that the following finite cubic
identity holds in the rectangular matrix algebra over `R`,

```text
DD^*D=lambda D,                                      (TDC3)
```

then

```text
p=lambda^(-1)DD^* in R                               (TDC4)
```

is a projection and satisfies

```text
p q_i=[(1-A_i)/2]q_i             for every i.         (TDC5)
```

Consequently

```text
B=1-2p                                                (TDC6)
```

is a self-adjoint unitary in `R` with `Bq_i=A_iq_i` for every `i`.

Thus the algebraic projection CRT does not require spectral calculus if
the defect row `D` can be made a scaled partial isometry.  The needed
condition is one explicit degree-three star-polynomial identity in the
fixed finite-support coefficients.

## Weighted and repeated columns

The same statement holds after replacing the columns by

```text
X_i=sqrt(w_i)q_i,              Y_i=sqrt(w_i)A_iq_i,   (TDC7)
```

for positive scalar weights.  When square roots are undesirable in a
rational group ring, an integer weight can instead be implemented by
repeating the corresponding column.  Compatibility is unchanged on each
pair of repeated columns, while `(TDC3)` becomes a finite algebraic frame
identity with integer coefficients.

This is only a sufficient criterion.  A general algebraic projection CRT
solution need not arise from a tight defect row, because the solution
projection may strictly dominate the support of `D` on unused complement
space.
