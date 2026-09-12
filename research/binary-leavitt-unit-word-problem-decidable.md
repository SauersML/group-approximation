---
rg: 2
id: binary-leavitt-unit-word-problem-decidable
kind: claim
title: The binary Leavitt unit group has decidable word problem
root: true
artifacts:
  - research/leavitt-normal-form-decides-unit-words-proof.md
---

Let

```text
R=L_(F_2)(1,2),              U=R^x.
```

The ring `R` has a computable normal form, and equality of two ring
expressions is decidable.  Consequently the word problem of the finitely
generated group `U` is decidable.

More generally, if `G` is finitely generated with decidable word problem,
then the restricted wreath product

```text
U^(G) semidirectProduct G
```

has decidable word problem.  Finite direct products and finite permutation
extensions of these groups do as well.  All internal free-reflection and
finite-wreath ambient groups used by the Leavitt reflection calculus
therefore have decidable word problem.
