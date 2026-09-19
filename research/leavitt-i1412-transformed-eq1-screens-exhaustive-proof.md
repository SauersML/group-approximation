---
rg: 2
id: leavitt-i1412-transformed-eq1-screens-exhaustive-proof
kind: route
title: Compare minimum and coarsening-maximal forests after every Eq3 substitution
target: leavitt-i1412-transformed-eq1-screens-exhaustive
requires:
  - leavitt-i1412-carrier-screens-exhaustive
---

For every Eq3 minimum scheme, retain its residual presentation and all
twelve original-generator images after the single-occurrence Tietze closure.
Transform the raw Eq1 free-product word by those images, deleting identity
syllables and merging newly adjacent same-copy syllables exactly as in the
paired carrier screen.  Deduplicate the resulting `(residual,word)` inputs.

For each transformed color word, independently compute

1. all globally minimum noncrossing partitions; and
2. all partitions maximal under same-color noncrossing coarsening, using the
   cofacial forest criterion.

The audit artifact performs this comparison without constructing any matrix
or group approximation.  MSI job `16680602` used one core for eight seconds
and returned

```text
transformed_inputs=223
minimum_schemes_total=395
maximal_schemes_total=395
nonminimum_maximal_inputs=0.
```

Therefore the minimum screen is exhaustive for every transformed Eq1 input,
not merely for the original raw Eq1 color word.

