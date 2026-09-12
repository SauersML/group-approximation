---
rg: 2
id: boolean-predicate-is-one-rank-jump
kind: claim
title: Every Boolean predicate is an affine matrix over F_2 whose rank jumps by exactly one on satisfying assignments
artifacts:
  - experiments/schur_clifford_rank_gate.py
  - research/artifacts/schur-clifford-predicate-rank-compiler-2026-08-19.md
distinct_from:
  finite-selector-gadget-induction-barrier: that proves a finite gadget cannot delete a selector character; this does not delete any character and instead makes an F_2 rank depend nonlinearly on the assignment, which is why the two do not conflict.
  one-hot-selector-parity-barrier: that concerns which selector parities a scalar relation can pin down; this concerns the rank of a commutation matrix and pins nothing down at the level of characters.
  tensor-affine-selector-pattern-barrier: that rules out affine selector patterns realizing a nonlinear support constraint; this puts the nonlinearity in a rank function rather than in a support constraint, so the barrier does not apply.
---

For every Boolean predicate `f : {0,1}^k -> {0,1}` there is an effectively
constructible square matrix `M_f(x)` over `F_2`, of size `(N+1) x (N+1)`, whose
entries are affine-linear forms in `x_1,...,x_k`, such that for every Boolean
assignment `x`

```text
rank_F2 M_f(x) = N + f(x).                                        (BPR1)
```

Moreover the upper-left `N x N` block `U_f(x)` is invertible for every `x`, so
the baseline rank `N` is assignment-independent and the predicate is carried by
exactly one extra rank.

For AND the construction collapses to

```text
M_and(x,y) = [[1, x],
              [y, 0]],        rank_F2 = 1 + xy.                   (BPR2)
```

**Why the rank normalization is the point.**  The equivalence between algebraic
branching programs and affine determinant representations is classical Valiant
territory and is not claimed here.  What `(BPR1)` adds is that the leading block
can be kept *invertible on every Boolean assignment*, so the predicate is not a
determinant that vanishes somewhere but a rank that moves by one.  That is what
makes `clifford-commutator-rank-is-packet-dimension` applicable, since a
commutator form of rank `r` gives spin dimension `2^r` and a rank that jumps by
one gives a dimension that doubles.

**Verification.**  `experiments/schur_clifford_rank_gate.py` builds the matrix
from a truth table and computes `rank_F2` by Gaussian elimination.  It has been
written to check `(BPR1)` exhaustively for every Boolean predicate of arity at
most three (all 4, 16 and 256 truth tables), as well as the minimal AND gate
and the one-hot predicate on three bits.  These are computational sanity checks;
the proof is the exact Schur-complement argument in
`boolean-predicate-is-one-rank-jump-proof`.
