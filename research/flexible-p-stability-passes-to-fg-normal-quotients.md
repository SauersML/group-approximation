---
rg: 2
id: flexible-p-stability-passes-to-fg-normal-quotients
kind: claim
title: Flexible P-stability passes to quotients with finitely generated kernel
distinct_from:
  alekseev-thom-stability-finite-actions-boundary: that treats the weaker stability-in-finite-actions notion and needs a Kazhdan kernel plus residual-finiteness hypotheses; this is flexible Hamming stability and only assumes that the kernel is finitely generated.
  amenable-quotient-preserves-metric-approximability: that passes approximation of a kernel up to an extension when the quotient is amenable; this passes stability of a group down to a quotient when the kernel is finitely generated.
  sofic-stable-implies-residually-finite: that derives residual finiteness from soficity plus stability; this is the quotient-permanence theorem used before that obstruction.
---

Let

```text
1 -> N -> G -> Q -> 1
```

be a short exact sequence with `N` finitely generated. If `G` is flexibly
P-stable in normalized Hamming distance, then `Q` is flexibly P-stable.

No soficity, residual finiteness, amenability, splitting, or property `(T)`
hypothesis is needed.

**ESTABLISHED 2026-08-31** by
[[alekseev-thom-flexible-p-quotient-permanence]].
