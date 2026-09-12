---
rg: 2
id: free-group-laplacian-refutes-regular-gap-fk-transfer
kind: claim
title: The free-group Laplacian refutes log-determinant transfer from a regular spectral gap
distinct_from:
  fk-transfer-needs-uniform-log-integrability: that gives the corrected general transfer criterion; this supplies an exact regular-microstate counterexample, including a version with every finite evaluation invertible.
---

For `F_2=<a,b>`, set

```text
L=4-a-a^(-1)-b-b^(-1).
```

Kesten's formula gives

```text
L(lambda_(F_2)) >= (4-2 sqrt(3)) I.
```

Nevertheless there is a sequence of exact finite-dimensional representations
`sigma_n` whose normalized characters converge to the regular character, for
which every `L(sigma_n)` is strictly invertible but

```text
(1/dim sigma_n) log det L(sigma_n) -> -infinity.
```

Thus a spectral gap in the regular representation, exact satisfaction of all
group relations, regular-character convergence, and finite invertibility do
not suffice for Fuglede--Kadison determinant transfer.
