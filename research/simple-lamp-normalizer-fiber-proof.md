---
rg: 2
id: simple-lamp-normalizer-fiber-proof
kind: route
title: Factor an automorphism implementer by the canonical regular permutation
target: simple-lamp-normalizers-have-unitary-multiplicity-fibers
requires: []
---

If `U` implements `alpha`, then

```text
(P_alpha^* tensor 1) U (lambda_Q(q) tensor 1)
 = (lambda_Q(q) tensor 1)(P_alpha^* tensor 1) U
```

for every `q in Q`.  Hence `C=(P_alpha^* tensor 1)U` belongs to
`lambda_Q(Q)' tensor M_m`, proving `(SMF2)`; the converse is immediate.

For `(SMF3)`, after absorbing `P_alpha` it is enough to compare
`1 tensor Fourier_m` with monomials in the product basis.  A monomial chooses
one entry from every row.  Each chosen entry has modulus at most
`m^(-1/2)`, so after optimizing diagonal phases the normalized real trace
overlap is at most `m^(-1/2)`.  Since both matrices are unitary,

```text
||U-M||_2^2=2-2 Re tr(M^*U)>=2-2/sqrt(m).
```

Formula `(SMF4)` follows because the canonical permutations multiply as the
automorphisms do and the multiplicity representation commutes with the lamp
algebra.
