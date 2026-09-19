---
rg: 2
id: normalized-quasitraces-detected-finitely
kind: claim
title: Absence of normalized quasitraces has a finitely generated obstruction seed
distinct_from:
  stw99-problem-i-quasitraces-are-traces: that asks whether quasitraces are additive; this compactness theorem concerns existence only and makes no linearity assertion.
artifacts:
  - research/artifacts/stw78-finite-quasitrace-seed-audit-2026-08-30.md
---

For every unital C-star algebra `B`, the following are equivalent:

1. `B` admits a normalized 2-quasitrace;
2. every finitely generated unital C-star subalgebra of `B` admits a
   normalized 2-quasitrace.

Consequently, if `B` has no normalized 2-quasitrace, there are finitely many
elements `b_1,...,b_m in B` such that

```text
C=C*(1,b_1,...,b_m)
```

has no normalized 2-quasitrace.  Every intermediate unital algebra
`C subset D subset B` is then quasitraceless as well.
