---
rg: 2
id: directed-unions-preserve-tracial-strict-comparison
kind: claim
title: Directed unions preserve strict comparison with respect to a compatible trace
distinct_from:
  robert-directed-unions-preserve-selflessness: Robert preserves the stronger model-theoretic selflessness property; this theorem assumes only strict comparison and proves its permanence directly by cutdown estimates.
  stw99-problem-xc-cstar-simple-strict-comparison: this is an abstract local-to-global permanence theorem, not the assertion that every C*-simple group admits suitable local pieces.
artifacts:
  - research/artifacts/stw90-strict-comparison-group-frontier-2026-08-30.md
---

Let `A` be a C*-algebra with trace `tau`, and suppose

```text
A = closure(union_i A_i)
```

for an upward directed family of C*-subalgebras, with `tau_i=tau|A_i`.
If every `A_i` has strict comparison with respect to `tau_i`, then `A` has
strict comparison with respect to `tau`.

No simplicity, uniqueness of trace, exactness, stable rank, or selflessness
is needed for this permanence statement.
