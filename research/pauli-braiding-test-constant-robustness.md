---
rg: 2
id: pauli-braiding-test-constant-robustness
kind: claim
title: The Pauli braiding test has perfect completeness and constant robustness
artifacts:
  - research/artifacts/schur-clifford-predicate-rank-compiler-2026-08-19.md
---

Natarajan--Vidick, *Robust self-testing of many-qubit states*,
arXiv:1610.03574, construct for every `N` a two-player Pauli braiding test
with `O(N)`-bit questions and `O(1)`-bit answers.  Instantiating its
anticommutation subtest with Magic Square gives perfect completeness.  Its
robustness is independent of `N`: a strategy accepted within `eta` of the
optimal value is, under local isometries, within

```text
delta=p(eta),                    p(eta)->0 as eta->0,
```

of a strategy containing `N` EPR pairs (the perfect implementation may use
one additional constant-size EPR ancilla).  The function `p` and all test
constants are universal, not functions of `N`.

The robustness conclusion is in state-dependent norm and up to local
isometries.  It is not by itself a normalized-HS group-presentation theorem;
that conversion is isolated downstream.
