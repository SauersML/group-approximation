---
rg: 2
id: toeplitz-expander-rounds-relative-clifford-cell
kind: route
title: Use polynomial Toeplitz-head Jacobi words to exactify each new Pauli cell uniformly
target: uniform-relative-clifford-tape-cell
requires:
  - toeplitz-head-jacobi-words-give-uniform-expanders
  - quantum-expander-rounds-relative-pauli-cell
---

At level `n`, evaluate the polynomial-length words `g_(j,n)` on the already
exactified old spin block. Their adjoint channel has the fixed gap supplied by
the first prerequisite. The polynomial derivations bound their commutation
defects with the proposed new cell by `poly(n)sqrt(E)`. Apply the second
prerequisite to push the cell into the old-spin commutant and exactify the
fixed Pauli table there. The rounding constant is independent of `n`; only
the permitted polynomial certificate factor remains. The nested extraspecial
subgroups keep the old spin factor unchanged and add one residual Pauli qubit,
which is precisely the conclusion of the target.

