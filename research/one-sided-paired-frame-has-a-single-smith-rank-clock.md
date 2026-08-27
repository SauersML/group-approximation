---
rg: 2
id: one-sided-paired-frame-has-a-single-smith-rank-clock
kind: claim
title: One-sided paired-frame transport is exactly one polynomial-controlled Pauli bit
artifacts:
  - experiments/paired_frame_one_sided_rank_clock.py
  - experiments/paired_frame_dual_character_clock.py
distinct_from:
  paired-frame-moving-kernel-is-a-rank-one-veronese-clock: that computes the orbit of one relation kernel; this keeps the coefficient packet fixed, transports only the source packet, and computes the Smith form of their combined commutator map.
  normal-closure-of-moving-kernels-kills-the-hard-form: that rules out imposing all moving kernels as relations in one module; this realizes each kernel as the internal relation kernel of a different conjugate frame inside a full-center packet, so only the intersection at that level is imposed.
  paired-hard-form-transverse-to-moving-clock: that obtains the degree-4n-2 scalar c_n squared by pairing a fixed covector with the moving line; this identifies the primitive Smith coordinate c_n itself, of degree 2n-1.
---

Let `R=F_2[x]`, `S=[[1+x^2,x],[x,1]]`, and `T=diag(S,S)`.  Write

```text
S^n=[[a_n,c_n],[c_n,d_n]].                                  (OSR1)
```

Take the paired Schur frame as a direct product of its source and coefficient
packets.  Hold the coefficient frame fixed and transport only the source
generators by `T^(-n)`.  Let

```text
C_n : wedge^2(R^4) -> R^3 source direct_sum R^3 coefficient (OSR2)
```

be the resulting six-coordinate central commutator map.  Then

```text
ker C_0=K_0,
ker C_n=K_0 intersect K_n=span_R{e_01,e_23}  for n>=1.        (OSR3)
```

Consequently `C_0` has rank three and every `C_n`, `n>=1`, has rank four.
More precisely, over the PID `R`, its nonzero Smith invariants are

```text
C_0:  1,1,1,
C_n:  1,1,1,c_n                 (n>=1).                         (OSR4)
```

The polynomial `c_n` is monic of degree `2n-1`.  Hence on an additive
character which is trivial on all words of degree below `2n-1`, the entire
new relative commutator coordinate is the sign of the single top word
`x^(2n-1)`.

This is the desired local rank-one groupification mechanism at the exact
algebraic level.  It uses no conditional relation and no chosen classical
map: the source and coefficient packet copies are honest group factors, and
the rank jump is caused by their one-sided relative position.  Transporting
both packet and character would instead be rank-neutral; keeping the
coefficient packet fixed is load-bearing.
