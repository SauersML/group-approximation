---
rg: 2
id: normalized-hs-null-loops-erase-determinant-phase
kind: claim
title: Normalized-HS null loops erase every determinant phase
distinct_from:
  hs-full-rank-scalar-defect-blocks-naive-rank-decoding: that uses small irrational scalar phases to refute direct HS-to-rank conversion; this uses rank-one winding to refute descent of determinant parity or a determinant central cover to the tracial quotient.
  complex-hyperlinear-leavitt-idempotent-mismatch: that is the characteristic-two failure of one explicit Leavitt idempotent; this is a coefficient-independent topological obstruction inside unitary matrix products.
artifacts:
  - notes/FALSE_DETERMINANT_INDEX_TO_PHASE_HS_EXTENSION.md
---

Let `d_n -> infinity` and

```text
N_2={ (U_n) in product_n U(d_n) : ||U_n-I||_(2,d_n) -> 0 }.
```

The determinant sign, determinant winding number, and determinant square-root
cover do not descend through the quotient by `N_2`.

Indeed

```text
U_n=diag(-1,1,...,1)
```

belongs to `N_2`, since `||U_n-I||_2=2/sqrt(d_n)`, but
`det(U_n)=-1` for every `n`. More strongly, the coordinatewise loop

```text
ell_n(t)=diag(exp(2 pi i t),1,...,1),       0<=t<=1,
```

lies uniformly in `N_2` and has determinant winding number one. Its lift to

```text
U(d_n)~={(U,z):z^2=det(U)}
```

starting over `(I,+1)` ends over `(I,-1)`. Hence the determinant double
cover has no splitting on the null subgroup and cannot be quotiented to a
central sign extension of the tracial matrix ultraproduct.

In fact `N_2` is path connected. Principal logarithms give
`U_n=exp(iH_n)` with `||H_n||_2 <= (pi/2)||U_n-I||_2`; then
`(exp(itH_n))_n` is a path in `N_2` from the identity to `(U_n)`. Therefore
every continuous homomorphism from `N_2` to a discrete phase group is
trivial.

This does not rule out a phase protected by an additional presentation-level
uniform spectral gap. It proves that normalized-HS topology and determinant
formalism alone cannot retain microscopic winding.
