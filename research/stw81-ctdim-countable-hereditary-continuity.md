---
rg: 2
id: stw81-ctdim-countable-hereditary-continuity
kind: claim
title: Continuous-trace shadow dimension is continuous along countable hereditary exhaustions
distinct_from:
  stw81-ctdim-extension-maximum: that is the two-piece formula for one ideal and its quotient; this theorem treats a countable increasing union of hereditary subalgebras, which need not be ideals, and rules out a new continuous-trace dimension jump at the limit.
artifacts:
  - research/artifacts/stw81-type-i-frontier-2026-08-30.md
---

Let `A` be a separable C-star algebra and let

```text
B_1 subset B_2 subset ... subset A
```

be hereditary C-star subalgebras of `A` with dense union.  Then

```text
ctdim(A) = sup_n ctdim(B_n).
```

Equivalently, if `(A_n,phi_n)` is a sequential inductive system of
separable C-star algebras in which every `phi_n` is injective and
`phi_n(A_n)` is a hereditary subalgebra of `A_(n+1)`, then

```text
ctdim(lim_n A_n) = sup_n ctdim(A_n).
```

In particular, the hereditary commutative-shadow hypothesis in Problem
LXXXI passes to such an inductive limit, and the limit has the hypothesis if
and only if every stage does.
