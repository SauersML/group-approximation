---
rg: 2
id: leavitt-paired-quotient-passes-relative-weight-test
kind: claim
title: The paired length-six Leavitt quotient passes the relative weight test and preserves both coefficient copies
distinct_from:
  leavitt-paired-relative-picture-local-census: That finite census locates the two torsion folds; this folds them into a global weight argument valid for pictures of arbitrary size.
  leavitt-length-six-full-support-torsion-candidate: That constructs the first candidate surviving the generic small-length theorems; this proves that the candidate nevertheless cannot violate Kervaire-Laudenbach.
artifacts:
  - research/leavitt-paired-quotient-passes-relative-weight-test-proof.md
---

For the paired relative presentation

```text
Q=<H,z | R_0,R_1>,                 H=G_0*G_1,
R_0=h_0 z h_1 z h_2 z^(-1),
R_1=k_0 z k_1 z k_2 z^(-1),
```

the natural homomorphism `H -> Q` is injective.  In particular the normal
closure of `R_0,R_1` has trivial intersection with each `G_i`, so these two
relators do not normally generate the degree-two kernel and the associated
length-six equation is not a Kervaire-Laudenbach counterexample.

