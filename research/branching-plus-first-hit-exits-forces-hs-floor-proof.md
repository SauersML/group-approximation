---
rg: 2
id: branching-plus-first-hit-exits-forces-hs-floor-proof
kind: route
title: Cancel one child against one exit and sum the triangular error ledger
target: branching-plus-first-hit-exits-forces-hs-floor
requires:
  - first-hit-carrier-contraction-ladder
  - free-root-top-boundary-reservoir-is-summable
  - fanizza-turing-bcs-signal-collapse
---

Combine `(BFE1)` and `(BFE2)`:

```text
2q_n <= q_(n+1)+q_n+delta_n+zeta_n,
```

so

```text
q_n <= q_(n+1)+delta_n+zeta_n.                         (1)
```

Iteration gives `(BFE5)`.  Now sum `(BFE3)` and use `(BFE4)`:

```text
eta sum_(n<N) q_n <= 1+sum_(n<N) epsilon_n.            (2)
```

Rearranging `(BFE5)` gives

```text
q_n >= q_0-sum_(j<n)(delta_j+zeta_j).
```

Substitute this in `(2)`.  The error with index `j` occurs for
`n=j+1,...,N-1`, exactly `N-1-j` times, proving `(BFE6)`.

Under `(BFE7)`, the two error sums in `(BFE6)` are at most `C_N sqrt(E)`.
If `q_0>=q_*` and `eta N q_*>1`, rearrangement and squaring give `(BFE8)`.
The argument uses only nonnegative scalar masses; all operator-algebraic work
is isolated in the four hypotheses.
