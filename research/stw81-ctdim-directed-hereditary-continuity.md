---
rg: 2
id: stw81-ctdim-directed-hereditary-continuity
kind: claim
title: Continuous-trace shadow dimension is continuous along arbitrary directed hereditary exhaustions
distinct_from:
  stw81-ctdim-countable-hereditary-continuity: that treats sequential hereditary exhaustions; this permits arbitrary directed indexing and does not assume a countable cofinal family.
  stw81-ctdim-extension-maximum: that is the two-piece formula for one ideal and its quotient; this theorem treats an arbitrary directed union of hereditary subalgebras, which need not be ideals, and rules out a new continuous-trace dimension jump at the limit.
artifacts:
  - research/artifacts/stw81-type-i-frontier-2026-08-30.md
---

Let `A` be a separable C-star algebra and let `(B_lambda)_(lambda in Lambda)`
be an upward-directed family of hereditary C-star subalgebras of `A` such
that

```text
A = closure(union_(lambda in Lambda) B_lambda).
```

Then

```text
ctdim(A) = sup_(lambda in Lambda) ctdim(B_lambda).       (H)
```

No countability, ordinal-continuity, or cofinality assumption on `Lambda` is
needed.

Equivalently, let `(A_lambda,phi_(lambda,mu))` be an arbitrarily indexed
directed inductive system with injective connecting maps whose images are
hereditary, and suppose its limit `A` is separable.  Then

```text
ctdim(A) = sup_lambda ctdim(A_lambda).
```

In particular, the hereditary commutative-shadow hypothesis in Problem
LXXXI passes to such a limit, and the limit has the hypothesis if and only
if every stage does.  Arbitrary ordinal hereditary exhaustions are a special
case, including ordinals of uncountable cofinality.
