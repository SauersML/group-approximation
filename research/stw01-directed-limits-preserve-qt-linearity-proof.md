---
rg: 2
id: stw01-directed-limits-preserve-qt-linearity-proof
kind: route
title: Combine quotient permanence with dense directed images
target: stw01-directed-limits-preserve-qt-linearity
requires:
  - stw01-local-trace-rigid-models-force-linearity
---

First, quasitrace linearity passes to quotients.  Indeed, if `q:C -> C/J`
is a quotient map and `sigma` is a bounded 2-quasitrace on `C/J`, then
`sigma q` is a bounded 2-quasitrace on `C`.  If all such quasitraces on `C`
are traces, `sigma q` is linear; surjectivity of `q` makes `sigma` linear.

Let `phi_i:A_i -> A` be the canonical map.  Its image is isomorphic to the
quotient `A_i/ker(phi_i)`, so the preceding paragraph shows that every
bounded 2-quasitrace on `phi_i(A_i)` is a trace.

The family of images is directed: for `i,j`, choose `k>=i,j`, and both
`phi_i(A_i)` and `phi_j(A_j)` lie in `phi_k(A_k)`.  Their union is dense in
the inductive limit.  Therefore each finite subset of `A` can be
simultaneously approximated in norm by one of the unital subalgebras
`phi_k(A_k)`.  The local-approximation theorem now applies.
