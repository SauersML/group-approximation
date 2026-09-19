---
rg: 2
id: leavitt-atlas-irreducible-purification-proof
kind: route
title: Select the least-energy simple summand of the coefficient algebra
target: leavitt-atlas-full-coefficient-purification
requires:
  - leavitt-regular-atlas-hyperlinearity-criterion
  - leavitt-regular-atlas-block-monomial-gap
---

Given a relative unitary `U`, decompose its block-coefficient algebra as

```text
D(U)=direct_sum_j(M_(r_j)(C) tensor I_(ell_j)).
```

After a multiplicity-space conjugacy,

```text
U=direct_sum_j(U_j tensor I_(ell_j)),
```

and the normalized average relator energy has the exact barycentric
decomposition

```text
E(U)=sum_j (r_j ell_j/k) E(U_j).
```

Therefore some simple summand satisfies `E(U_j)<=E(U)`. By definition, the
block coefficients of this summand generate all of `M_(r_j)(C)`. Also

```text
max_s ||pi_(U_j)(s)-1||_2^2 <= |bar S| E(U_j).
```

Applying this selection at every stage of a vanishing-energy certificate
preserves vanishing maximum defect. The selected dimensions must tend to
infinity: otherwise a bounded subsequence would contradict the positive
fixed-dimensional atlas gaps (equivalently the bounded-complexity escape law).
The converse is immediate from the regular-atlas criterion.
