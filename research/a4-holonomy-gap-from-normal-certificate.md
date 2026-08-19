---
rg: 2
id: a4-holonomy-gap-from-normal-certificate
kind: route
title: Five conjugacy checks and six local covariance semantics force complete chart-frame collapse
target: atlas-a4-holonomy-coherence-gap
requires:
  - atlas-a4-normal-certificate-compiler
  - atlas-a8-five-conjugacy-hs-collapse
  - atlas-a8-six-transvection-commutant-gap
---

Put

```text
eta'_n = max_(s in S\{t23})||r_s(V_n)-1||_2,
delta'_n = ||V_n(t23)-1||_2.
```

The compiler gives

```text
eta'_n <= C_cert eta_n,
delta'_n <= C_col (||sigma_n(q_19243)-1||_2+eta_n).
```

Apply `atlas-a8-five-conjugacy-hs-collapse`:

```text
max_(s in S)||V_n(s)-1||_2
 <= eta'_n+delta'_n
 <= C_cert eta_n
    + C_col (||sigma_n(q_19243)-1||_2+eta_n)
 -> 0.                                                   (1)
```

By the local semantic readout `(A4-NCERT-3)`, for every `s in S`,

```text
||[U_n,lambda_(k_n)(s)]||_2
 = ||U_n lambda(s) U_n^* lambda(s)^*-1||_2
 <= ||V_n(s)-1||_2+C_sem eta_n
 -> 0.                                                   (2)
```

Now use `atlas-a8-six-transvection-commutant-gap`.  Since `|S|=6`, `(2)` gives
explicitly

```text
dist_2(U_n,lambda_(k_n)(A8)')
 <= 15 sqrt(6)
    (max_(s in S)||V_n(s)-1||_2+C_sem eta_n)
 -> 0.                                                   (3)
```

Choose a nearest commutant element `Y_n`.  For each of the two fixed raw-S3
covariance generators `h_a,h_b`,

```text
||[U_n,lambda(h)]||_2 <= 2||U_n-Y_n||_2 -> 0.
```

Hence `a_n^2+b_n^2->0`, stronger than the required `limsup<1/128`, and
`atlas-a4-holonomy-coherence-gap` follows.

The live one-leaf compiler portfolio is therefore completely local: five
frozen conjugacy-loop defects, one collision-transvection defect, and six
opcode-to-covariance semantic defects.  Full A8 table consistency,
representation rounding, invariant-sector bookkeeping and a global decoder
hypothesis have all disappeared.
