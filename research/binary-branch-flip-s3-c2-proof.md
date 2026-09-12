---
rg: 2
id: binary-branch-flip-s3-c2-proof
kind: route
title: Compute the Leavitt branch-flip Weyl word and extend by the Pauli tensor swap
target: binary-branch-flip-weyl-has-s3-c2-model
requires:
  - closed-compression-fold-loop-retains-s3-gauge
  - one-arm-range-sum-whitehead-has-marked-model
---

Expand `(BFW1)` and use `t_is_j=delta_ij`.  The two square terms vanish and
the cross terms are `s_0t_0` and `s_1t_1`, whose sum is one; this proves
`u^2=1`.  Multiplying `u` by each `s_i` and each `t_i` proves the remaining
four equations in `(BFW2)`.

Direct multiplication of the three elementary `2 by 2` blocks gives
`F_ab=[[0,u],[u,0]]`, because the characteristic is two and `u^2=1`.
Conjugating a single off-diagonal block then proves `(BFW4)`.  This is an
explicit ordinary matrix calculation; no opposite-root commutator formula
is assumed.

For the finite model, `(1 2)` fixes the equal last two entries of `J` and
interchanges `C_0,C_1`.  The Pauli tensor swap interchanges both `X` arms
and both controlled `Z` arms because the controlling `J=-1` projection is
fixed.  Conjugation of permutations gives

```text
(1 2)(0 2)(1 2)=(0 1),
```

which is `(BFW7)`.  All old rows remain exact by the preceding closed-loop
model.  Finally multiplying `F` by the already present character
permutation `(1 2)=W_0W_1W_0` leaves identity on `C^3` and tensor swap on
the Pauli factors.  This proves that the extension is the stated finite
`S_3 x C_2` actor and completes the countermodel.

