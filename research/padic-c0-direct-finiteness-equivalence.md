---
rg: 2
id: padic-c0-direct-finiteness-equivalence
kind: claim
title: Modular group algebras and their p-adic c0 completions are directly finite simultaneously
distinct_from:
  stable-finiteness-reduces-to-prime-field: that changes the coefficient field in the universal matrix conjecture; this keeps the prime field fixed and identifies finite-support direct finiteness with direct finiteness of one non-Archimedean completion, group by group and at every matrix size.
  leavitt-stable-finiteness-equals-direct-finiteness: that collapses matrix size for the one Leavitt unit group algebra by an internal corner embedding; this compares a modular group algebra with its p-adic c0 completion for every group and does not collapse matrix size.
artifacts:
  - research/artifacts/leavitt-packet-trace-and-compression-2026-08-24.md
---

For every prime `p`, every group `G`, and every `n >= 1`, let

```text
C_p(G)=c_0(G,Z_p)
```

be the p-adic Banach convolution algebra.  Then

```text
M_n(F_p[G]) is directly finite
  <=>
M_n(C_p(G)) is directly finite.
```

In particular `F_p[G]` is directly finite if and only if `C_p(G)` is
directly finite.  Reduction modulo `p` is finite-support on `c_0`; lifting a
modular one-sided inverse produces a product in `1+pC_p(G)`, while lifting a
reverse-product defect produces an idempotent of norm strictly between zero
and one.  These are the two directions of the equivalence.

The completion is therefore an exact reformulation of the
positive-characteristic problem, not an escape from it.
