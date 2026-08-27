---
rg: 2
id: hyperlinear-fp-recognition-complete-iff-nonhyperlinear-group
kind: claim
title: Hyperlinearity of finitely presented groups is Pi-zero-two complete iff a non-hyperlinear group exists
distinct_from:
  approximation-property-recognition-dichotomy: that gives, on finite presentations, only Sigma-zero-one hardness on side (B); this upgrades side (B) to Pi-zero-two completeness by routing the negative seed through the MF-safe compiler, and is open only because hyperlinearity of that compiler's positive branch is not yet recorded.
  hyperlinear-recognition-undecidable: that asserts side (B); this is the two-sided statement identifying the exact level on side (B).
---

OPEN (conditional on [[mf-compiler-positive-branch-is-hyperlinear]]).
Exactly one of:

```text
(A) every group is hyperlinear, and HYP_fp is the set of all codes;
(B) some group is not hyperlinear, and HYP_fp is Pi^0_2-complete,
    NONHYP_fp Sigma^0_2-complete.
```

The direction (B) => "some non-hyperlinear group" is trivial.  For the
converse, a non-hyperlinear group yields a finitely presented one
(cover lemma), which seeds the MF-safe compiler: on `FIN` the output
contains the seed and is not hyperlinear (heredity), on `INF` it is the
compiler's positive branch, hyperlinear by the hypothesis.  Membership is
[[nonhyperlinear-presentation-codes-have-a-sigma2-upper-bound]].
