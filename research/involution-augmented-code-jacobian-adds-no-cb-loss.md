---
rg: 2
id: involution-augmented-code-jacobian-adds-no-cb-loss
kind: claim
title: Adding involution residuals introduces no new completely bounded linear inverse
distinct_from:
  quadratic-overlay-has-uniform-linearized-synchronization-gap: that proves the Hilbert-space gap for the reflection presentation; this splits its domain into involution-normal and tangent directions and identifies an explicit cb inverse on the new normal summand.
  complete-overlay-row-newton-is-a-code-riesz-multiplier: that isolates the unresolved tangent cb multiplier; this proves that passing to selfadjoint contractions does not enlarge that multiplier problem.
  aggregate-cut-compression-stores-boundary-as-involution-defect: that creates a contraction tuple with positive involution residual; this shows how that residual enters the linearized correction without a new dimension-dependent constant.
---

ESTABLISHED LINEAR REDUCTION.  Let `S_1,...,S_L` be an exact commuting
code tuple of reflections, and let `h_i=h_i^*` be perturbations.  Split

```text
 h_i^+=(h_i+S_ih_iS_i)/2,       h_i^-=(h_i-S_ih_iS_i)/2.   (IAJ1)
```

The linearization of the involution equation is

```text
 d(X_i^2-I)_S(h_i)=S_ih_i+h_iS_i=2S_ih_i^+.            (IAJ2)
```

It annihilates the tangent part `h_i^-`, and on its compatible range it has
the explicit right inverse

```text
 r_i |-> h_i^+=(1/2)S_ir_i.                            (IAJ3)
```

For the normalized operator row norm this inverse has cb norm exactly
`1/2`:

```text
 ||(1/L)sum_i(h_i^+)^2||_infinity^(1/2)
 =1/2||(1/L)sum_i r_i^2||_infinity^(1/2).              (IAJ4)
```

After this normal correction, subtract its image in the parity,
equality, and complete-pair equations.  Those fixed-width derivatives and
normalized complete-pair derivatives have a dimension-independent row
bound `C_0`.  The remaining compatible residual lies in the image of the
tangent variables `h^-`.  Hence, if the tangent code-Riesz/equality inverse
has cb row norm `C_T`, the full involution-augmented Jacobian has a right
inverse on its range with norm at most

```text
 1/2+C_T(1+C_0/2).                                     (IAJ5)
```

Thus selfadjoint contraction variables add no new linear cb obstruction.
The unresolved linear estimate remains exactly `(CRM3)`, the tangent
code-Riesz multiplier.

For basin capture it is unnecessary to drive the positive involution
residual to zero during every Newton step.  If a contraction tuple has

```text
 epsilon_inv=(1/L)sum_i tau(I-X_i^2)=o(1),             (IAJ6)
```

then coordinatewise spectral signs satisfy average squared displacement at
most `epsilon_inv`.  Every fixed-width relator changes by `o(1)` under this
final rounding.  Therefore the residual produced by aggregate-cut block
compression may be treated as a vanishing forcing floor while the tangent
Newton iteration corrects the balanced relations, and rounded only once at
the end.

This does not prove the nonlinear Newton theorem.  Its smallest remaining
estimate is the tangent row/column inverse `(CRM3)` together with stability
of that inverse under a vanishing normal forcing term.  No separate
involution-layer Riesz transform or operator-norm sign control is required.
