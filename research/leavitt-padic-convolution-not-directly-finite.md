---
rg: 2
id: leavitt-padic-convolution-not-directly-finite
kind: claim
title: The 2-adic c0 convolution algebra of the Leavitt unit group is not directly finite
distinct_from:
  leavitt-unit-group-algebra-not-directly-finite: that asks for a finite-support one-sided inverse over F_2; this asks for one in the 2-adic c0 completion, and the p-adic equivalence proves the statements equivalent without identifying their witnesses term by term.
  leavitt-group-algebra-not-stably-finite: that asks for a failure in a finite matrix algebra over the modular group algebra; this is a scalar failure in the 2-adic Banach completion.
artifacts:
  - research/artifacts/leavitt-packet-trace-and-compression-2026-08-24.md
---

For `G=L_(F_2)(1,2)^x`, exhibit `A,B in C_2(G)=c_0(G,Z_2)` with

```text
AB=1,        BA != 1.
```

By `padic-c0-direct-finiteness-equivalence`, this claim is equivalent to
`leavitt-unit-group-algebra-not-directly-finite`.  Passing to the completion
does not weaken the problem.

## Attempts

The equivalence is the only construction presently available.  It converts
a witness in either algebra into the conclusion in the other, but supplies no
new finite-support pair and no convergent correction series for the Leavitt
defect.  In particular the recursive corner tail remains nonzero at every
finite stage, and no p-adic contraction of that tail has been established.
