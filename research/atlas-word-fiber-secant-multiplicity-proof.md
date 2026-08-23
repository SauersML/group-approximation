---
rg: 2
id: atlas-word-fiber-secant-multiplicity-proof
kind: route
title: Span the exact right-commutant orbit by finite word-fiber chords
target: atlas-word-fiber-secants-have-full-multiplicity-absorber
requires:
  - atlas-full-relator-data-factor-through-double-commutant-gauge
  - atlas-aligned-word-jacobian-has-full-multiplicity-absorber
---

The right-gauge part of the double-commutant identity is literal equality:

```text
(UC)rho_2(b)(UC)^*=U rho_2(b)U^*
```

for `C in rho_2(A8)'`.  First-chart letters do not involve `U`, so
multiplication proves `(AFS1)` for every word, simultaneously.

Let `A=rho_2(A8)'`.  Every element of a finite-dimensional C-star algebra is
a linear combination of unitaries (apply the four-unitary decomposition to
its self-adjoint real and imaginary parts).  Since `-I` is unitary,

```text
U=(-1/2)(U(-I)-U)
```

lies in the chord span.  For any unitary `C in A`, both `UC-U` and `U` lie in
the span, hence so does `UC`.  Linear combinations now give `UA`, proving
`(AFS2)`.

At an aligned frame, `U_0` sends the `sigma` isotypic block to the
`alpha sigma` block as `A_sigma tensor B_sigma`.  Right multiplication by

```text
I_(V_sigma) tensor M_(d_sigma k)
```

ranges through `A_sigma tensor Hom(M_sigma,M_(alpha sigma))` because
`B_sigma` is unitary.  Minimal Fourier compression is the scalar coefficient
of `A_sigma` times the arbitrary multiplicity matrix, exactly as in
`(AJM5)`.  This proves `(AFS3)` and the full-range assertion.  Finally
`U_0 in U_0 A` is invertible, so no subspace can be shrunk by the chord span.

