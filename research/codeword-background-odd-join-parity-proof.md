---
rg: 2
id: codeword-background-odd-join-parity-proof
kind: route
title: Cancel every dual word in the background and localize its residual to its own blocks
target: codeword-background-keeps-odd-join-parity-cheap
requires:
  - orthogonal-odd-cut-join-amplifies-boundary-linearly
  - join-of-odd-cuts-softens-an-entire-anchor-row
---

Use `H=direct_sum_(j=1)^L K_j`, with

```text
 K=C^2_sign tensor C^2_mem,
 A_0=Z tensor I,
 P=I tensor |0><0|,
 C=X tensor |0><0|+I tensor |1><1|,
 S=I tensor X.                                          (CBP1)
```

Let `A=direct_sum_j A_0`.  Define `B_i` to be `C` on block `i` and
`S^(c_i)` on every block `j!=i`.  The background `S^(c_i)` commutes with
`A_0`; exactly as in the orthogonal-join obstruction,

```text
 ((B_i-AB_iA)/2)^2=P_i.                                (CBP2)
```

The join is `P` on every block.  If `c_i=1`, `B_i` swaps `P` outward on all
`L-1` other blocks; if `c_i=0`, it does not.  Since the unnormalized block
value is `||[P,S]||_F^2=4` and `dim H=4L`, averaging gives `(CBJ1)`.
The calculations for `(CBJ2)--(CBJ3)` are the same block count, using

```text
 ||[A_0,C]||_F^2=8,    ||[C,S]||_F^2=8.                (CBP3)
```

Now fix `h in C_L^perp`.  On a block `j notin h`, its ordered parity word is

```text
 S^(sum_(i in h)c_i)=I.                                (CBP4)
```

On block `j in h`, exactly one background factor has been replaced by `C`.
The word there is `S^a C S^b`, with
`a+b=c_j mod 2` because `sum_(i in h)c_i=0`.  If `c_j=0`, it is `C` or
`SCS` and has squared Frobenius distance `4` from `I`.  If `c_j=1`, it is
`CS` or `SC` and has squared distance `8`.  Summing these block values and
dividing by `4L` proves the exact formula `(CBJ4)`.

Finally, `Bbar_i=direct_sum_j S^(c_i)` is an exact commuting tuple and its
row products are identity by `(CBP4)`.  The only difference from `B_i` is
on block `i`; `||C-I||_F^2=4` and `||C-S||_F^2=8`, proving `(CBJ7)`.
