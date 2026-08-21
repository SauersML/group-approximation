---
rg: 2
id: osin-relative-ball-double-coset-proof
kind: route
title: Turn a double-coset collision into one protected four-letter element
target: osin-relative-ball-injectivity-protects-sign-double-cosets
requires: []
artifacts:
  - research/artifacts/relative-small-cancellation-occurrence-support-2026-08-21.md
---

**Established by citation plus one normal-form calculation.**  Osin,
*Small cancellations over relatively hyperbolic groups and embedding
theorems*, arXiv:math/0411039v3, Lemma 5.1(2), states that for every prescribed
`N` the small-cancellation constants can be chosen so that the quotient map is
injective on all elements of relative length at most `N`.

If `(ORB2)` fails, then for some `a,a' in H_X`, `b,b' in H_Z` and signs
`p_0,p_1`,

```text
gamma(a p_0 b)=gamma(a' p_1 b').
```

Therefore `gamma` kills

```text
(a')^(-1)a p_0 b(b')^(-1)p_1^(-1).
```

Combine the first two peripheral terms into one `H_X` letter and the middle
two into one `H_Z` letter.  The relative length is at most four.  The element
is nontrivial in `G` by `(ORB1)`, contradicting ball injectivity.

