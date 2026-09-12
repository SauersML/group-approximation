---
rg: 2
id: nested-schur-multiplicity-wire-globalizes-selectors-proof
kind: route
title: The external multiplicity algebra is contained in the packet commutant
target: nested-schur-multiplicity-wire-globalizes-selectors
requires: []
---

On an `A_f` isotypic decomposition

```text
H=directSum_lambda S_lambda tensor M_lambda,
```

the external multiplicity algebra is

```text
directSum_lambda I_(S_lambda) tensor End(M_lambda)
  subset rho(A_f)'.
```

Every selector `z_i` belongs to `A_f`, so every operator in this multiplicity
algebra commutes with `rho(z_i)`. If all generators of the next packet act in
that algebra, its selector generators commute with all current selectors.
Induction gives `(NSG1)`. Jointly commuting involutions have a common spectral
decomposition, so all BCS constraints on the transported family reduce to a
mixture of classical characters, proving the final statement.

