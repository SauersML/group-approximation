---
rg: 2
id: reflection-corner-encoding-exposes-real-payload-correlations
kind: claim
title: Reflection dilation recovers a unitary corner but exposes real payload correlations
distinct_from:
  central-corner-block-is-not-a-group-word: that proves a controlled block cannot be a word in the bare control and payload; this computes the exact trace character of the standard two-by-two reflection dilation.
  free-label-orthogonalization-erases-payload-trace: that masks payload by free labels and loses it completely; this retains the payload in a matrix corner but shows why the ambient reflection character is not regular.
---

**ESTABLISHED.**  For a unitary `u` in a finite tracial algebra `(M,tau)`,
put

```text
r_u=[[0,u],[u^*,0]],              r_1=[[0,1],[1,0]],
e=[[1,0],[0,0]].                                                   (RCE1)
```

Then `r_u` is a self-adjoint involution and

```text
e r_u r_1 e=u e.                                                   (RCE2)
```

Thus the payload is recovered exactly in the `e`-corner.  But for two
payloads,

```text
r_u r_v=diag(uv^*,u^*v),
tau_2(r_u r_v)=Re tau(uv^*).                                      (RCE3)
```

Odd products of the reflections are off-diagonal and have trace zero.
Consequently the ambient reflection character is not the regular character
unless all exposed real correlations happen to vanish.  Adding the grading
`diag(1,-1)` names `e`, but then it also makes the payload-readable corner
available; it does not mask the unwanted even-word moments.

