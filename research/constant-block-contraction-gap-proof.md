---
rg: 2
id: constant-block-contraction-gap-proof
kind: route
title: Compress to the constant-label projection and apply the reverse triangle inequality
target: constant-block-contraction-gap
requires: []
---

Write `p = (1/4) J_4 tensor 1`.  Since `J_4^2 = 4 J_4`, `p` is a projection, and
`tau(p) = 1/4` so `||p||_2 = 1/2`.

**`(CBG1)`.**  For `S=(S_ij) in M_4(N)` the normalized trace gives
`||S||_2^2 = (1/4) sum_i tau_N((S^*S)_ii) = (1/4) sum_(i,j) ||S_ij||_(2,N)^2`.
Apply this to `S = T - K(C)`, whose `(i,j)` block is `T_ij - C/2`.

**`(CBG2)`.**  The operator `1 tensor C` commutes with `p`, and
`K(C) = 2 p (1 tensor C)`, so `K(C) p = 2 p^2 (1 tensor C) = K(C)` and

```text
||K(C)||_2^2 = 4 tau(p (1 tensor C^*C)) = 4 . (1/4) tau_N(C^*C) = ||C||_(2,N)^2.
```

Right-compressing by `p` cannot increase the Hilbert--Schmidt norm, since
`||Xp||_2 <= ||X||_2 ||p||_op = ||X||_2`.  Hence

```text
||T - K(C)||_2 >= ||(T - K(C))p||_2 = ||Tp - K(C)||_2
               >= ||K(C)||_2 - ||Tp||_2
               >= ||C||_(2,N) - ||T||_op ||p||_2
               >= ||C||_(2,N) - 1/2.
```

`(CBG3)` follows because the left side is nonnegative.

**Pauli instance.**  Under `(CBG4)`, `(CBG1)` says
`||T_n - K(C_n)||_2 -> 0`.  Fix any block; the reverse triangle inequality in
`N_n` gives `| ||T_(ij,n)||_2 - ||C_n||_2/2 | -> 0`, and
`||T_(ij,n)||_2 = 1/sqrt(8)`, so `||C_n||_2 -> 2/sqrt(8) = 1/sqrt(2)`.  Then
`(CBG3)` forces `liminf ||T_n - K(C_n)||_2^2 >= (1/sqrt(2)-1/2)^2`, and
`(1/sqrt(2)-1/2)^2 = 1/2 - 1/sqrt(2) + 1/4 = 3/4 - 1/sqrt(2) > 0`.  This
contradicts `||T_n - K(C_n)||_2 -> 0`.

This is sections 2 and 3 of `TRUE_TRACE_FLAT_COMMON_BLOCK_CONTRACTION_GAP.md`,
which had no node in this graph.
