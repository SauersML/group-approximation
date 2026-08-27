---
rg: 2
id: uniform-clock-reflection-block-proof
kind: route
title: Compress the controlled clock reflection onto the uniform zero-flag line
target: uniform-clock-reflection-block-encodes-game-hamiltonian
requires:
  - two-copy-bcs-game-hamiltonian-dominates-fanizza-signal
---

After replacing rational weights by repetitions, write
`H=M^(-1) sum_j L_j`.  For each clock value set

```text
C_j=(1-L_j) tensor 1 + L_j tensor X.
```

The two summands occupy the orthogonal projections `1-L_j` and `L_j`.
Since `X=X^*=X^(-1)`, it follows that `C_j=C_j^*=C_j^(-1)`.
The clock-block diagonal sum `C=sum_j e_(jj) tensor C_j` is therefore also a
self-adjoint unitary.

Let `s=M^(-1/2) sum_j e_j`, so `q_s=|s><s|`, and let
`q_0=|0><0|=(1+Z)/2`.  The two elementary compressions are

```text
q_s e_(jj) q_s = M^(-1) q_s,
q_0 (1-X) q_0 = q_0.
```

Moreover `1-C_j=L_j tensor (1-X)`.  Thus, with
`Q=q_s tensor q_0` on the clock and flag factors,

```text
Q(1-Re C)Q
 = sum_j M^(-1) L_j tensor Q
 = H tensor Q.
```

This is `(UCR4)`.  Each `P_(c,a)` entering the Fanizza losing projections is
an explicit rational product of commuting involutions, while the clock and
flag matrix units have rational coefficients in the displayed matrix
amplification.  Hence all entries of `C`, and therefore the reflection
`V_m`, are rational finite-support group-algebra expressions.

Finally the established two-copy inequality `D_R<=C_m H_m`, tensored with
the rank-one clock/flag carrier and combined with the compression identity,
gives `(UCR5)`.  This proves every clause of the target.
