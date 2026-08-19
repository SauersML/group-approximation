---
rg: 2
id: a4-holonomy-gap-from-normal-certificate
kind: route
title: Five transvection conjugacy checks propagate the 19243 readout to complete chart-frame collapse
target: atlas-a4-holonomy-coherence-gap
requires:
  - atlas-a4-normal-certificate-compiler
  - finite-normal-certificate-hs-collapse
  - atlas-a8-six-transvection-normal-certificates
  - atlas-a4-19243-parabolic-normal-closure
---

Use the six standard transvections

```text
S={t01,t10,t12,t21,t23,t32},       b=t23.
```

By `atlas-a8-six-transvection-normal-certificates`, these generate `A8` and
every `s in S` is one conjugate of `b`; hence the normal-certificate theorem
has collision multiplicity exactly

```text
M=1.
```

For the compiler output put

```text
eta'_n = max_(s in S\{t23})||r_s(V_n)-1||_2,
delta'_n = ||V_n(t23)-1||_2.
```

Then `(A4-NCERT-1)` and `(A4-NCERT-2)` give

```text
eta'_n <= C_cert eta_n,
delta'_n <= C_col (||sigma_n(q_19243)-1||_2+eta_n).
```

Apply `finite-normal-certificate-hs-collapse`, including the tautological
`t23` certificate at zero defect:

```text
max_(s in S)||V_n(s)-1||_2
 <= eta'_n+delta'_n
 <= C_cert eta_n
    + C_col (||sigma_n(q_19243)-1||_2+eta_n)
 -> 0.                                                   (1)
```

The decoder `(A4-NCERT-3)` therefore gives

```text
dist_2(U_n,lambda_(k_n)(A8)') -> 0.                    (2)
```

Choose a nearest commutant element `Y_n`.  For each of the two fixed raw-S3
covariance generators `h_a,h_b`,

```text
||[U_n,lambda(h)]||_2 <= 2||U_n-Y_n||_2 -> 0.
```

Hence `a_n^2+b_n^2->0`, stronger than the required `limsup<1/128`, and
`atlas-a4-holonomy-coherence-gap` follows.

The live proof portfolio has therefore lost the 20160-state table entirely.
Its only genuinely new compiler mathematics is: expose six standard chart
transvection opcodes, verify **five fixed conjugacy loops**, read `t23` from
collision 19243, and decode collapse of those six generators to the regular
chart commutant.
