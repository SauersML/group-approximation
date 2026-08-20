---
rg: 2
id: fanizza-nonmember-signal-is-not-a-separated-mark-proof
kind: route
title: Specialize the signal bound to a perfect strategy and audit the theorem interface
target: fanizza-nonmember-signal-is-not-a-separated-mark
requires:
  - fanizza-turing-bcs-signal-collapse
---

Set `epsilon=0` in `(FTB1)`.  Positivity gives

```text
0 <= phi(D) <= C_m * 0 = 0,
```

which is `(FNM1)`.  The statement of
`fanizza-turing-bcs-signal-collapse` names only the BCS systems, their strategy
states and the projection `D`; it contains neither a group presentation nor a
nontrivial word.  Hence marked separation is an additional proof obligation,
not a consequence of the citation.
