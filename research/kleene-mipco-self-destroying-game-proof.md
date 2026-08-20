---
rg: 2
id: kleene-mipco-self-destroying-game-proof
kind: route
title: Search finite strategies for the fixed point and flip coRE soundness
target: kleene-mipco-self-destroying-game
requires: []
artifacts:
  - research/artifacts/kleene-self-destroying-hs-pcp-boone-2026-08-20.md
---

Finite dimensions and rational approximations to finite-dimensional quantum
strategies are enumerable.  Since the acceptance probability is continuous
and the threshold is strict, existence of a strategy of value greater than
`theta` is recursively enumerable.

Apply Kleene's recursion theorem to the machine that computes its own game
`V_*` and runs this search.  If it halts, it found a finite strategy of value
greater than `theta`, whence

```text
omega_co(V_*) >= omega_*(V_*) > theta.
```

But halting activates `(KMG1)` and gives `omega_co(V_*)<=s<theta`, a
contradiction.  The machine therefore does not halt.  Nonhalting completeness
gives `omega_co(V_*)>=c`, and failure of the search gives
`omega_*(V_*)<=theta`, proving `(KMG2)`.

