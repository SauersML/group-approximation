---
rg: 2
id: fpbs-uniqueness-pivotals-are-dangling-bridges-proof
kind: route
title: Close a bridge between two infinite pieces and contradict uniqueness by deletion tolerance
target: fpbs-uniqueness-pivotals-are-dangling-bridges
requires: []
---

Complete direct proof. For an edge `e` let `A_e` be the event that `e` is open
and `C \ e` has two infinite components. The configuration with `e` closed has
at least two infinite clusters. By deletion tolerance of Bernoulli percolation,

```text
P_p(N_infinity >= 2) >= ((1-p)/p) P_p(A_e).
```

Uniqueness makes the left side zero, so `P_p(A_e) = 0` for each of the countably
many edges, and the union is null.

If `e` is open and pivotal for `{o <-> x}` with `o, x in C`, closing `e`
disconnects `o` from `x`. So `e` disconnects `C`, and by the first part the side
of `C \ e` containing `o`, or the side containing `x`, is finite. Such an edge is
a bridge with `o` or `x` on its finite side, which gives
`N_(o <-> x) <= N_o + N_x`.
