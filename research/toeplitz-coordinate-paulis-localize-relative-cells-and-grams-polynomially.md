---
rg: 2
id: toeplitz-coordinate-paulis-localize-relative-cells-and-grams-polynomially
kind: claim
title: Toeplitz coordinate Paulis localize relative cells and Fanizza Grams with polynomial depth loss
artifacts:
  - research/artifacts/toeplitz-coordinate-pauli-gram-localization-2026-08-21.md
distinct_from:
  toeplitz-head-jacobi-words-give-uniform-expanders: that constructs canonical spin expanders from Clifford normalizer words; this uses the honest coordinate Pauli words and is therefore insensitive to multiplicity twists.
  thompson-pauli-prefix-rounding-has-polynomial-cost: that obtains the same inverse-linear Pauli bound from Thompson-addressed sites; this derives it inside the Toeplitz finite heads and also applies it directly to the Fanizza compressed Gram.
  kazhdan-transitive-pauli-actor-localizes-one-mixed-word: that gives constant localization from one orbit prototype under an exact uniformly gapped actor; this uses all coordinate Pauli rows, costs `sqrt(n)`, and needs no actor exactification.
---

On an exact depth-`n` Toeplitz Pauli prefix, a proposed new cell whose
coordinate cross-commutators have RMS defect `epsilon_n` is
`O(sqrt(n)epsilon_n)`-close to the old-spin commutant.  Fixed Pauli-pair
stability then rounds the cell in the residual factor.  Polynomial Toeplitz
word/derivation lengths make the complete loss polynomial in `n`, uniformly
in ambient dimension and multiplicity.

Moreover, for `X=(E-H)UE`, `q=E-X^*X`, if `E,H` commute with the old
coordinate Paulis, then

```text
dist_2(q,old-spin commutant)
 <=sqrt(2n)
   ((1/(2n))sum_i(||[U,P_i]||_2^2+||[U,Q_i]||_2^2))^(1/2).
```

Thus coordinate commutators localize the Fanizza Gram without any Clifford
normalizer orientation.  The remaining compiler must identify the native
Fanizza chord `U` with the Toeplitz new-cell incidence on the same C18 cut.
