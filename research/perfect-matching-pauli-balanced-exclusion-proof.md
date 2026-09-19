---
rg: 2
id: perfect-matching-pauli-balanced-exclusion-proof
kind: route
title: Convert Pauli parity failures to bad checks and invoke robust erasure cleaning
target: balanced-parity-excludes-perfect-matching-pauli-mixtures
requires:
  - erasure-cleaning-rounds-all-projective-parity-valleys
  - unbalanced-pair-sum-overlay-has-scalar-syndrome-escape
---

Pauli orthogonality gives squared distance two from the identity whenever
the vector label of a word is nonzero; a wrong scalar sign has squared
distance four.  Repeating each original check `Theta(M)` times among
`Theta(M^2)` total faces therefore bounds `(BPM3)` by a universal multiple
of the balanced energy.  This is exactly the term missing from the
unbalanced all-equal-syndrome escape.  Pair-sum labels are `s_a+s_b`, so
they cannot weaken this bound.

For a good row `h_a`, `sum_i h_a(i)v_i=0`.  Pairing this equality with
`v_j` under `omega` gives

```text
 sum_i h_a(i)B_(i,j)=0
```

for every `j`.  Thus outside the full bad-check set `E` from `(BPM3)`, every
row of `B` satisfies the kernel equation required by
`erasure-cleaning-rounds-all-projective-parity-valleys`.  Pauli commutators
have squared defect zero or four, so its `beta` is one quarter of
complete-pair energy.  Substitution in the projective rounding estimate
proves `(BPM5)`.  The constants survive central direct sums because all
estimates integrate against central trace.
