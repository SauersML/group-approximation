---
rg: 2
id: sofic-action-free-wreath-counterexample-proof
kind: route
title: Turn a sofic coset atlas into canonical free-wreath microstates
target: sofic-coset-action-refutes-sl3-central-dual
requires:
  - centralizer-hnn-is-free-generalized-wreath
  - gkp-free-wreath-permanence
  - central-letter-averages-matrix-range-separators
---

Assume the action in `(SCD1)` is sofic.  The free generalized-wreath
permanence theorem and `(SCD2)` make `G_p` sofic, hence hyperlinear, with a
canonical approximation.

Suppose every canonical approximation satisfied `(LCG3)`.  The established
route

```text
central dual => selected matrix-range capture
             => large-prime relative-commutant collapse
             => G_p nonhyperlinear
```

would contradict the canonical approximation just constructed.  Therefore
one canonical sequence violates `(LCG3)`.  Equivalently, selected
matrix-range capture fails along a subsequence; applying
`central-letter-averages-matrix-range-separators` gives separators satisfying
the normalization, operator bound, stable-letter asymptotic centrality, and
fixed positive gap stated in the claim.
