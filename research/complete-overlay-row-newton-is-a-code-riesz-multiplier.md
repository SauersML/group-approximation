---
rg: 2
id: complete-overlay-row-newton-is-a-code-riesz-multiplier
kind: claim
title: Complete-overlay row Newton is a vector-valued code Riesz multiplier problem
distinct_from:
  quadratic-overlay-has-uniform-linearized-synchronization-gap: that bounds the inverse in normalized Hilbert--Schmidt norm by orthogonality of character blocks; this identifies the stronger completely bounded row norm required on the diffuse cut
  balanced-overlay-diffuse-square-function-newton: that is nonlinear and begins away from an exact base; this computes the exact-base linear operator whose cb or BMO control is its first missing input
---

At an exact code representation, the transverse inverse of the complete-pair
Jacobian is a vector-valued Schur/Fourier multiplier on the code-character
decomposition.

Indeed, on the matrix block from `chi` to `psi`, put `z=chi+psi`.  For
`S=supp(z)`, the complete-pair coboundary is

```text
 b_ij=z_j a_i-z_i a_j.                                  (CRM1)
```

Modulo the simultaneous-conjugation kernel, it has the explicit inverse

```text
 a_i = (1/|S|) sum_(j in S) b_ij       for i notin S,
 a_i-avg_(j in S)a_j
     = (1/|S|) sum_(j in S) b_ij       for i in S.       (CRM2)
```

Because `|S|>=delta L`, `(CRM2)` is uniformly bounded on every individual
character block both in Hilbert--Schmidt norm and in operator row/column
norm.  Equality-expander inversion is likewise a Markov Green average with
coefficient mass bounded by the inverse expander gap.

Globally, however, `S` depends on `(chi,psi)`.  Assembling `(CRM2)` across
all character blocks is exactly a vector-valued Schur multiplier whose
symbol is the normalized support vector of `chi+psi`--a code analogue of a
Riesz transform.  Hilbert--Schmidt orthogonality gives `(QLS1)` for free,
but a uniform bound on each block does not imply a uniform completely
bounded norm of the assembled Schur multiplier.

Therefore the linear input needed by
`balanced-overlay-diffuse-square-function-newton` is precisely one of:

```text
 uniform cb row/column bound for the code Riesz multiplier,              (CRM3)
```

or a uniform noncommutative-BMO bound plus a John--Nirenberg truncation whose
exceptional projection is summable in the Newton iteration.  Characterwise
averaging alone cannot be quoted as `(CRM3)`; doing so silently replaces an
`L_2` direct-sum estimate by an `L_infinity` Schur-multiplier estimate.
