---
rg: 2
id: word-energy-domination-is-free-subgroup-membership
kind: claim
title: Universal word-energy domination is free-subgroup membership
distinct_from:
  nontrivial-words-have-no-relation-energy-domination: that excludes one presentation-relative inequality; this characterizes exactly when an arbitrary finite word list gives such an inequality, with an explicit linear dimension bound for counterexamples.
  finite-context-energy-certificate-iff-word-trivial: that allows the finite contextual test list to vary and characterizes normal-closure membership; this fixes the list and characterizes subgroup membership, including when a trivial quotient word still has no certificate on the specified tests.
artifacts:
  - notes/PROPERTY_T_FREE_CONTEXT_ENERGY_2026-09-07.md
---

For words `v_1,...,v_k,w` in a finite-rank free group `F`, set
`E_v(U)=(v(U)-I)^*(v(U)-I)`. Then

```text
w in <v_1,...,v_k>
  iff exists C>=0, forall d>=1, forall U in U(d)^m,
        E_w(U) <= C sum_j E_(v_j)(U).
```

A product expression for `w` of length `L` in `v_j^{+/-1}` supplies
`C=L^2`. If membership fails, a permutation tuple of dimension at most
`1+|w|+sum_j |v_j|` has a unit vector fixed by every `v_j(U)` with target
squared displacement exactly `2`.

This is an elementary written theorem. It has no Lean certification claim
and supplies no non-MF existence theorem.
