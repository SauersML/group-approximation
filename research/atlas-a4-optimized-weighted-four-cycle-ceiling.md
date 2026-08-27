---
rg: 2
id: atlas-a4-optimized-weighted-four-cycle-ceiling
kind: claim
title: Some reciprocal-weighted four-cycle trace ceiling beats the raw S3 wall
distinct_from:
  atlas-a4-anisotropic-four-cycle-ceiling: that target fixes the symmetric t21 weights 24,24,24 before optimization; this target lets the packet proof choose any sharp diagonal weights adapted to the directions it controls most cheaply.
  atlas-a4-four-cycle-dirichlet-ceiling: that target uses one unweighted four-cycle scalar; this target retains the exact three-direction tradeoff relevant to t21 and the direct t12 readout.
---

For the normalized exact-regular A4 context-network sequence, put

```text
D_ij(n)=1-Re tau_n(V_n(tij)).
```

Prove that there exist positive constants

```text
c_01,c_23,c_30 > 0
```

with

```text
4/c_01 + 4/c_23 + 16/c_30 <= 1                         (W)
```

such that

```text
limsup_n
  (c_01 D_01(n) + D_12(n) + c_23 D_23(n) + c_30 D_30(n))
 < 1/256.                                               (A4-OPT-W)
```

By `atlas-a8-t21-diagonal-energy-envelope`, condition `(W)` is exactly the
sharp diagonal family produced by the audited eight-letter `t21` identity.
Thus the upstream A4/collision analysis may spend its trace budget
anisotropically instead of proving an unnecessarily predetermined combination.

The old fixed target is the special choice

```text
(c_01,c_23,c_30)=(24,24,24).
```

## Attempts

- **Optimize weights together with the SOS dual.** Treat `c_01,c_23,c_30` as
  outer-loop variables subject to `(W)` while the inner finite SDP searches for
  the trace ceiling. A direction that the 19243 collision controls strongly may
  carry a large coefficient, buying smaller coefficients on the hard
  transverse directions.
- **Use reciprocal coordinates.** Put `p_i=l_i^2/c_i` for `l=(2,2,4)`. Then
  `p_01+p_23+p_30<=1` and `c_i=l_i^2/p_i`; the weight search is a simplex
  optimization rather than an arbitrary positive cone.
- **Do not seek a better symmetric word constant.** The sharp-envelope theorem
  proves that `24` is already minimax-optimal among diagonal consequences of
  this one word. Any symmetric improvement must use an additional group
  identity or a non-diagonal quadratic correlation.