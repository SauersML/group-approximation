---
rg: 2
id: a4-holonomy-gap-from-four-cycle-trace-compiler
kind: route
title: Four scalar transvection traces force chart-frame collapse
target: atlas-a4-holonomy-coherence-gap
requires:
  - atlas-a4-four-cycle-trace-compiler
  - unitary-trace-energy-transfer
  - atlas-a8-four-cycle-commutant-gap
---

Let

```text
B_n=V_n(t23),
T_n(t)=V_n(t),       t in {t01,t12,t30}.
```

The collision readout `(A4-TRACE-2)` and the normalized-network hypotheses give

```text
1-Re tau_n(B_n) -> 0,
```

hence

```text
||B_n-1||_2^2=2(1-Re tau_n(B_n))->0.                  (1)
```

Rewrite `(A4-TRACE-1)` as

```text
sum_(t in {t01,t12,t30}) Re tau_n(T_n(t))
 >= 3 Re tau_n(B_n)-C_tr eta_n.
```

Apply `unitary-trace-energy-transfer` with `m=3` and
`eps=C_tr eta_n`.  It yields

```text
sum_(t in {t01,t12,t30}) ||T_n(t)-1||_2^2
 <= 3||B_n-1||_2^2+2C_tr eta_n -> 0.                 (2)
```

Together with `(1)`, all four covariance opcodes in

```text
T={t01,t12,t23,t30}
```

have vanishing Hilbert--Schmidt defect.  Since

```text
V_n(t)=U_n lambda_(k_n)(t) U_n^* lambda_(k_n)(t)^*,
```

unitary invariance gives exactly

```text
||V_n(t)-1||_2
 = ||U_n lambda_(k_n)(t)-lambda_(k_n)(t)U_n||_2.
```

The established `atlas-a8-four-cycle-commutant-gap` therefore implies

```text
dist_2(U_n,lambda_(k_n)(A8)')->0.                    (3)
```

Choose `Y_n` in that commutant with `||U_n-Y_n||_2->0`.  The two fixed raw-S3
involutions `h_a,h_b` defining the target covariance coordinates lie in the
A8 chart.  Thus for either `h`,

```text
||[U_n,lambda_(k_n)(h)]||_2
 <= 2||U_n-Y_n||_2 ->0.
```

Consequently

```text
a_n^2+b_n^2 ->0,
```

which is stronger than the required `limsup < 1/128`.  Hence the scalar trace
compiler alone proves `atlas-a4-holonomy-coherence-gap`.
