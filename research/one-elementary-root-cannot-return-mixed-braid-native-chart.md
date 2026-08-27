---
rg: 2
id: one-elementary-root-cannot-return-mixed-braid-native-chart
kind: claim
title: One elementary root cannot return the mixed-braid residual to the native Whitehead chart
artifacts:
  - research/one-root-mixed-braid-native-target-proof.md
distinct_from:
  one-elementary-root-cannot-return-mixed-braid-chart: that rules out return to the signed source by tracking two complementary entries; this closes the separate native-target equation which that claim explicitly leaves open.
  mixed-braid-gauge-cancellation-misses-signed-hecke-targets: that treats the bare residual and its visible one-root cancellation; this permits one arbitrary elementary root of unrestricted coefficient depth before comparison with the native chart.
  one-nonnormal-dressing-cannot-preserve-moving-full-gram: that starts with a word already transporting the source to the native target and characterizes its dressings; this proves that the mixed-braid residual cannot be made into such a transporter by one root.
---

**ESTABLISHED ONE-ROOT NATIVE-TARGET FENCE.**  Retain the asymmetric
mixed-braid residual

```text
P=[[q_0,1],[q_1,q_0]]_(7,9),
q_i=s_it_i,                                             (ORN1)
```

and the first literal native Whitehead

```text
J=J_1=[[1-q_0,y_1],[x_1,1-e_00]]_(7,8),
x_1=s_00t_0,  y_1=s_0t_00,  e_00=s_00t_00.             (ORN2)
```

For every actor pair `a!=b` and every binary-Leavitt coefficient `c`, put

```text
R=x_ab(c)=1+cE_ab.                                     (ORN3)
```

Then

```text
J^(-1) R P notin Norm(L_0),                            (ORN4)
```

and hence, for the signed Hecke Reynolds projection
`Q=e_(L_0,lambda_0)`,

```text
(RP)Q(RP)^(-1) != JQJ^(-1).                            (ORN5)
```

The obstruction is the first intrinsic fixed-space term

```text
F_1=<e_2,e_7>_R
```

of the signed Hecke group.  Since `J=J^(-1)`, a hypothetical native return
would make `g=JRP` normalize `L_0` and therefore preserve `F_1`.  But

```text
JP e_7=x_1e_8+q_1e_9.                                  (ORN6)
```

One elementary root changes `Pe_7` in at most one additional coordinate.
After applying `J`, that correction can affect the `{7,8}` block or the
`9` coordinate, but not both.  Thus at least one of the two nonzero
components `x_1e_8`, `q_1e_9` survives in `JRP e_7`; consequently

```text
JRP e_7 notin F_1.                                     (ORN7)
```

This closes the native-target equation deliberately left open by
`one-elementary-root-cannot-return-mixed-braid-chart`.  Together the two
claims show that the first asymmetric mixed-braid residual cannot reach
either the signed source or its active `J_1` translate after one arbitrary
root occurrence, with no restriction on coefficient depth.  The next live
continuation needs at least two additional nonnormal occurrences or one
genuinely three-coordinate occurrence before the native comparison.

No Property `(T)`, Kazhdan input, trace hypothesis, stability theorem,
enumeration, literature result, local computation, or Lean compilation is
used.

DERIVATION
one-root-mixed-braid-native-target-proof
