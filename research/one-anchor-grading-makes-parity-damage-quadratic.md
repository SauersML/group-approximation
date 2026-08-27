---
rg: 2
id: one-anchor-grading-makes-parity-damage-quadratic
kind: claim
title: One-anchor grading makes parity, pair, and sign damage quadratic
distinct_from:
  random-code-anchor-pinchings-contract-exact-transverse-energy: that proves the exact-base linear spectral gap and a coarse global sign-rounding cost; this identifies the nonlinear remainder at one anchor and shows that its first derivative vanishes.
  dense-complete-pair-remainders-are-cb-quadratic: that factors the globally averaged dense Newton remainder; this gives the exact local Z2-graded formulas, including bounded parity faces and spectral sign.
  balanced-overlay-local-alternating-projections-contract: that assumes an operator tube around an exact representation; this derives the algebraic quadratic structure before an exact base has been chosen.
---

ESTABLISHED.  Let `A` and `B_1,...,B_m` be reflections in a finite tracial
von Neumann algebra.  Split every `B_i` into its even and odd parts for
`Ad(A)`:

```text
 X_i=(B_i+A B_i A)/2,       Y_i=(B_i-A B_i A)/2.         (OAG1)
```

Then

```text
 [A,X_i]=0,       A Y_i A=-Y_i,
 X_i^2+Y_i^2=1,  X_iY_i+Y_iX_i=0.                       (OAG2)
```

Let `Phi_A=(I+Ad(A))/2`.  For a word `W=B_1...B_m`, expand it by replacing
each factor with `X_i+Y_i`.  The pinching kills exactly the terms containing
an odd number of `Y` factors.  Consequently

```text
 X_1...X_m-1
 =Phi_A(W-1)-sum_(|S| even, |S|>=2) W_S(X,Y),            (OAG3)
```

where `W_S` is the ordered word using `Y_i` on `S` and `X_i` elsewhere.
In particular a parity relator incurs no term linear in the anchor-odd
parts.  Since `m` is fixed, if `max_i ||Y_i||_infty<=kappa`, then

```text
 ||X_1...X_m-1||_2
 <=||W-1||_2+C_m kappa sum_i ||Y_i||_2.                  (OAG4)
```

For two reflections the exact commutator identity is

```text
 [X_i,X_j]=Phi_A([B_i,B_j])-[Y_i,Y_j].                  (OAG5)
```

Thus the complete-pair layer is likewise a CP-contracted linear residual
plus a two-odd-factor remainder.

Finally suppose `||Y_i||_infty<=kappa<1`.  Then
`X_i^2=1-Y_i^2 >=(1-kappa^2)1`, so `X_i` is invertible.  With
`S_i=sgn(X_i)` one has the operator identity

```text
 |S_i-X_i|=1-|X_i|
            =(1-X_i^2)/(1+|X_i|)
            =Y_i^2/(1+|X_i|),                           (OAG6)
```

and hence

```text
 ||S_i-X_i||_2
 <= kappa/(1+sqrt(1-kappa^2)) ||Y_i||_2.                 (OAG7)
```

Therefore hard reflection-rounding also has zero first derivative in the
anchor-odd direction on an operator-small block.  Combining `(OAG3)` with
a telescoping replacement of `X_i` by `S_i` preserves the form `(OAG4)`
with a different constant depending only on the fixed face width.

This removes the apparent linear face damage from the earlier triangle
audit.  It does not by itself sum the two-odd-factor terms over the sparse
parity layer; that exact remaining estimate is recorded in
`sparse-anchor-odd-fourth-moment-is-the-renormalization-gate`.
