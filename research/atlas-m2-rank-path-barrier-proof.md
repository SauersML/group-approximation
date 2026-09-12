---
rg: 2
id: atlas-m2-rank-path-barrier-proof
kind: route
title: Apply rank Lipschitzness to kernel words and replace one phase block at a time
target: atlas-m2-kernel-phases-have-rank-path-barrier
requires:
  - atlas-multiplicity-two-joint-kernel-slice-is-empty
---

For invertible matrices, `rank(U^-1-V^-1)=rank(U-V)`.  Telescoping a product
shows that changing one relative gauge from `U` to `V` changes a conjugated
chart letter by rank at most `2 rank(U-V)`.  The q14 word contains two such
letters and collision `19243` contains four.  Hence

```text
rank(q_14(U)-q_14(V))<=4 rank(U-V),
rank(q_19243(U)-q_19243(V))<=8 rank(U-V).              (RPBP1)
```

If `V in H_N`, compare q14 at `A_N` and `V`.  Its ranks are respectively `N`
and zero, so `(RPBP1)` gives `rank(A_N-V)>=N/4`, which is `(RPB2)` after
division by `8N`.  The collision comparison between `B_N` and `C_N` gives
`rank(B_N-V)>=2N/8=N/4`, the same normalized bound.

Laurent evaluation and rank are additive on direct sums.  This proves every
identity in `(RPB3)`--`(RPB4)`.  Minimizing `max(N-j,2j)` gives `(RPB5)`.
The same two Lipschitz comparisons, followed by minimization over arbitrary
`T in C_m` and `V in H_m`, give `(RPB7)`.
