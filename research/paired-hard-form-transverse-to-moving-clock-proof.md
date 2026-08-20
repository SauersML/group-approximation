---
rg: 2
id: paired-hard-form-transverse-to-moving-clock-proof
kind: route
title: Evaluate the forbidden form on the closed moving-line formula
target: paired-hard-form-transverse-to-moving-clock
requires:
  - paired-frame-moving-kernel-is-a-rank-one-veronese-clock
  - support-packet-paired-word-frame-exposes-forbidden-rank
artifacts:
  - experiments/paired_frame_moving_kernel_orbit.py
---

Direct substitution in the symbolic support-packet commutator matrix gives

```text
F_plus(101,011)=F_minus(011,101)
  = [[0,0,1,0],
     [0,0,0,0],
     [1,0,0,0],
     [0,0,0,0]],
F_minus(101,101)=0.
```

The first matrix is the alternating covector `e_02^*`, proving `(HTK1)`.
The coefficient of `e_02` in `(MVK4)` is `c_n^2`, which proves `(HTK2)`.
The degree formula `deg c_n=2n-1` from the alternating-shear theorem gives
`(HTK3)`.

The verifier asserts all three evaluated forms, computes the polynomial
pairing at every audited level, and checks its degree through level 47 using
exact bitset arithmetic over `F_2[x]`.
