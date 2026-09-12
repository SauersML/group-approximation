---
rg: 2
id: spectral-range-hall-deficit-is-cutoff-monotone-proof
kind: route
title: Larger spectral windows only enlarge collective block ranges
target: spectral-range-hall-deficit-is-cutoff-monotone
requires: []
---

For `a<=b`, spectral calculus gives the inclusion

```text
K_a <= K_b.
```

Fix a source-block subset `A` and a target block `j`.  Every vector of the form

```text
p_j T x,  T in K_a,  x in direct_sum_(i in A) H_i
```

is therefore also obtained with `T in K_b`.  Hence the corresponding target
range-span at cutoff `a` is contained in the one at cutoff `b`, so its
dimension cannot decrease when the cutoff grows.

Summing those target dimensions and subtracting from the fixed source
dimension gives `(SRH1)`.  Taking the maximum over `A` preserves the same
monotonicity.

Finally, in finite dimension the spectral subspace `K_a` is constant while
`a` stays between consecutive eigenvalues of `L`.  Therefore every block
range-span and every range-Hall deficiency is constant on those intervals as
well.
