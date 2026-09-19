---
rg: 2
id: compression-preimage-whitehead-gauge-proof
kind: route
title: Compute the coefficient preimages and conjugate the two packet charts
target: compression-preimage-whitehead-preserves-gauge
requires:
  - leavitt-whitehead-20x20-compression-cell
  - literal-whiteheads-give-gauged-moving-bridge-table
---

The Leavitt relations give the four coefficient calculations in
`(CPW1)--(CPW2)` directly.  Since `alpha` is the rootwise homomorphism
implemented by the compression cell, applying it to the three factors of
each `W_ab` proves `(CPW3)`.

For completeness, on the first two-coordinate preimage the direct block
multiplication is

```text
W_87(s_0,t_0) = [[1-s_0t_0,s_0],[t_0,0]],
```

and its square is the identity: `t_0s_0=1`,
`(1-s_0t_0)s_0=0`, and `t_0(1-s_0t_0)=0`.  Thus this is an actual
opposite-root partial Whitehead, not a formal coefficient substitution.

Now conjugate the source and range cuts by `T_i^(-1)`.  Tensor
multiplication on the two restrictions of `T_i` gives

```text
(N_B tensor B)(N_W tensor D_W)(N_A tensor A)^(-1)
 =N_J tensor (B D_W A^(-1)),
```

which is `(CPW4)`.  Taking `A=B=1` and a fixed nontrivial involution `D`
gives the stated exact finite amplification.  Direct sums preserve every
displayed identity and keep the normalized Hilbert--Schmidt distance of
`D` from the identity fixed, proving the corona fence.

