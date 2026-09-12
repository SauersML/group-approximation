---
rg: 2
id: copy-codes-one-sided-table-identities-proof
kind: route
title: Relay s outputs p(s,m0) and the sink reads relay s0, and the transposed network returns q(m0,s0)
target: copy-codes-make-one-sided-table-identities-strict
requires: []
artifacts:
  - research/artifacts/boolean-core-alphabets-and-network-coding-2026-09-12.md
---

Lemma 6.1 of the artifact.
- **Forward composite.** Every forward relay applies `pi_(m0)`, so relay `s` outputs `p(s,m0)`. The
  sink applies `pi_(s0)` and returns `p(s0,m0)`. So `Dec(T_f)` holds iff `(s0,m0)` lies in the class
  of `(1,1)`.
- **Reverse composite.** Reverse relays apply `pi_(s0)` and the sink applies `pi_(m0)`, returning
  `q(m0,s0)`.
- **Failure of `Enc`.** When `(m0,s0)` and `(1,1)` lie in different `T_r`-classes, a `q` taking two
  different values on them witnesses the failure.
