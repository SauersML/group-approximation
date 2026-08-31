---
rg: 2
id: hyperbolic-rf-not-flexibly-p-stable
kind: claim
title: Some residually finite hyperbolic group is not flexibly P-stable
distinct_from:
  alekseev-thom-stability-finite-actions-boundary: that records Theorem A(ii), where a Kazhdan normal kernel controls stability in finite actions; this records Theorem A(i) and its unconditional flexible-permutation-stability counterexample.
  literal-group-not-stable-in-finite-actions: that is a concrete sofic non-residually-finite group failing the weakest permutation-stability notion; the present witness is residually finite and hyperbolic, and the conclusion is failure of flexible P-stability.
  sofic-stable-implies-residually-finite: that is the general sofic-plus-stability obstruction used in the proof; this is the hyperbolic residually finite counterexample produced from it by a Rips extension.
---

There exists a hyperbolic, residually finite group `G` which is not flexibly
P-stable.

Here flexible P-stability means that every asymptotic homomorphism
`sigma_n:G -> Sym(X_n)` in normalized Hamming distance can be corrected by
genuine actions on finite supersets `Y_n` with

```text
X_n subseteq Y_n,       |Y_n \ X_n| / |X_n| -> 0.
```

This is an existential theorem; the source obtains `G` from Wise's
residually finite Rips construction rather than giving a fixed finite
presentation.

**ESTABLISHED 2026-08-31** by
[[alekseev-thom-rips-flexible-p-instability-proof]].
