---
rg: 2
id: polynomial-context-witness-via-free-subgroup
kind: route
title: Build linear-size support-word witnesses without a quotient word algorithm
target: finite-context-relator-energy-misses-nontrivial-words
requires:
  - word-energy-domination-is-free-subgroup-membership
artifacts:
  - notes/PROPERTY_T_FREE_CONTEXT_ENERGY_2026-09-07.md
  - experiments/word_energy_certificate.py
  - experiments/test_word_energy_certificate.py
---

Write each fixed polynomial context as
`p_j=sum_(q in supp p_j) c_(j,q) q`, and form the finite free-group list

```text
V={q^{-1} r_j q : j, q in supp p_j},       H=<V> <= F(S).
```

Since `H <= <<R>>`, the promise `w!=1` in `G=F(S)/<<R>>` implies
`w notin H`. The prerequisite supplies permutation matrices and a unit
vector with `v(U)xi=xi` for every `v in V` and squared target displacement
`2`. Multiplying the equation
`(q(U)^* r_j(U) q(U)-I)xi=0` by `q(U)` yields
`(r_j(U)-I)q(U)xi=0`. Linearity annihilates every polynomial-context
residual. This is exactly the target's conclusion, including the
contradiction to any added scalar slack below `2`.

The dimension is at most

```text
1+|w|+sum_(j,q in supp p_j) (2|q|+|r_j|).
```

Unlike the quotient-ball construction, this witness can be computed from
the finite words by free-subgroup folding: the promise guarantees the
nonmember branch. It requires no algorithm for the word problem in `G`.
Without the promise, a nonmember certificate still refutes this fixed
inequality, but does not prove that `w` is nontrivial in `G`. A member
report for the enlarged support-word list does not establish domination
by the original polynomial contexts, since their coefficients may cancel.
