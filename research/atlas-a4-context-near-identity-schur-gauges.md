---
rg: 2
id: atlas-a4-context-near-identity-schur-gauges
kind: claim
title: Every normalized exact A4 context admits a near-identity exact Schur gauge to its literal chart pair
artifacts:
  - research/artifacts/a4-context-virtually-free-compiler-2026-08-19.md
---

Let `sigma_n` be the exact regular context-network representations supplied by
`atlas-a4-context-exact-regular-normalization`.  For any one of the thirty A4
context vertices `c`, write `(a_c,b_c)` for its order-three/order-two
generators and `(A_c,B_c)` for the literal pair in the adjacent A8 chart to
which the two cyclic edge groups attach.

Then there are exact unitary A4 intertwiners `Z_(c,n)` from the context
representation to the chart restriction such that, uniformly over the fixed
thirty contexts,

```text
||Z_(c,n)-I||_2 -> 0.                                 (A4-LOCAL-GAUGE)
```

On the canonical three-dimensional coherence sectors, each `Z_(c,n)` is a
pure multiplicity gauge:

```text
W_chart Z_(c,n) W_c^* = I_3 tensor V_(c,n).
```

Hence after simultaneous exactification and regular normalization there is no
asymptotically nontrivial qutrit rotation hidden in an overlap edge.  Any
remaining continuous freedom of the A4 network lives only on multiplicity
wires; the fixed three-state register is rigidly synchronized to the literal
chart pair.