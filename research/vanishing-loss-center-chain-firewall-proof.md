---
rg: 2
id: vanishing-loss-center-chain-firewall-proof
kind: route
title: Pass vanishing-loss cuts to the fixed ultraproduct corner and apply the affine rank gap
target: vanishing-loss-center-chain-authentication-hits-affine-firewall
requires:
  - center-chain-mixed-hecke-overlap-is-common-pauli-source
  - two-shared-gauge-selector-rows-have-an-affine-rank-obstruction
---

For projections `E'<=E` in a normalized tracial matrix algebra,

```text
||E-E'||_2^2=tau(E-E').                               (1)
```

Thus every subprojection which discards vanishing ambient trace represents
the same projection as `E` in the tracial ultraproduct.  A finite
intersection costs at most the sum of the discarded traces, so the same
observation applies to the common source and range cuts used for both
rows.  Since the canonical matrix moments converge to the regular group
trace, the ultraproduct values of the fixed Hecke words are precisely the
regular operators `Q,P,S_1,S_2`.

The retained relative-polar identity identifies the two external gauges up
to the stated row and commutator errors.  On a retained common source of
ambient trace `t'`, divide ambient Hilbert--Schmidt norms by `sqrt(t')`.
The robust inequality `(TSG4)` from
`two-shared-gauge-selector-rows-have-an-affine-rank-obstruction` then gives

```text
(epsilon_1+epsilon_2)/sqrt(t') >= 1/3-o(1).            (2)
```

Here the `o(1)` includes the polar and mixed-Pauli errors used to conjugate
the two gauges.  The exact common-source calculation gives
`t=tau(Q)=tau(e)/128>0`; a cut of ambient trace loss `eta` has
`t'>=t-eta`.  Hence

```text
epsilon_1+epsilon_2
  >= (1/3-o(1))*sqrt(t-eta).                           (3)
```

The right side stays positive when `eta->0`.  This proves both the
ultraproduct assertion and the quantitative firewall.  Squaring `(3)` in
the regime where its right side is positive also gives

```text
t'<=9(epsilon_1+epsilon_2)^2+o(1),
eta>=t-9(epsilon_1+epsilon_2)^2-o(1),                 (4)
```

which is the claimed full-loss form.
