---
rg: 2
id: wedderburn-integer-chord-proof
kind: route
title: Count the positive target rank in every Wedderburn multiplicity block
target: finite-relative-commutant-chord-is-bounded-integer-feasibility
requires:
  - chord-regauging-is-relative-commutant-feasibility
---

The commutant of `(WIF1)` is

```text
M'=direct-sum_lambda (1_(n_lambda) tensor M_(m_lambda)(C)). (WIF4)
```

Suppose first that `(CRF2)--(CRF3)` holds and write

```text
(1+Z)/2=direct-sum_lambda (1_(n_lambda) tensor f_lambda),
k_lambda=rank(f_lambda).
```

The rank of the product with the `lambda` component of `e_(i,s)` is
`r_(i,s,lambda)k_lambda`.  Summing over the orthogonal Wedderburn blocks and
using `(CRF3)` gives `(WIF3)`.

Conversely, given a solution of `(WIF3)`, choose any rank-`k_lambda`
projection `f_lambda in M_(m_lambda)(C)` and define

```text
Z=2 direct-sum_lambda (1_(n_lambda) tensor f_lambda)-1.
```

Then `Z in M'=A_0' intersect A_1'`, and `(WIF3)` gives every positive
conditional rank in `(CRF3)`.  Since both spectral projections sum to the
same separator atom, the negative conditional ranks agree as well.
`chord-regauging-is-relative-commutant-feasibility` supplies the two endpoint
unitaries.  This proves the equivalence.

For the Pauli example, `(WIF1)` has one block with `n_1=2,m_1=1`.
The positive projection of an involution in `(WIF4)` is therefore either zero
or the identity on `C^2`, which proves the stated failure at rank one.
