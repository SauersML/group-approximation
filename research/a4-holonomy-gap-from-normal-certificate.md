---
rg: 2
id: a4-holonomy-gap-from-normal-certificate
kind: route
title: Finite normal certificates propagate the 19243 readout to complete chart-frame collapse
target: atlas-a4-holonomy-coherence-gap
requires:
  - atlas-a4-normal-certificate-compiler
  - finite-normal-certificate-hs-collapse
  - atlas-a4-19243-parabolic-normal-closure
---

Let `M` be the maximum number of collision occurrences in the fixed
normal-generation certificates `(A4-NCERT-0)`.  For the compiler output put

```text
eta'_n = max_(s in S)||r_s(V_n)-1||_2,
delta'_n = ||V_n(b)-1||_2.
```

Then `(A4-NCERT-1)` and `(A4-NCERT-2)` give

```text
eta'_n <= C_cert eta_n,
delta'_n <= C_col (||sigma_n(q_19243)-1||_2+eta_n).
```

Apply `finite-normal-certificate-hs-collapse` to the fixed certificate family:

```text
max_(s in S)||V_n(s)-1||_2
 <= eta'_n+M delta'_n
 <= C_cert eta_n
    + M C_col (||sigma_n(q_19243)-1||_2+eta_n)
 -> 0.
```

The decoder `(A4-NCERT-3)` therefore gives

```text
dist_2(U_n,lambda_(k_n)(A8)') -> 0.
```

Choose a nearest commutant element `Y_n`.  For each of the two fixed raw-S3
covariance generators `h_a,h_b`,

```text
||[U_n,lambda(h)]||_2 <= 2||U_n-Y_n||_2 -> 0.
```

Hence `a_n^2+b_n^2->0`, stronger than the required `limsup<1/128`, and
`atlas-a4-holonomy-coherence-gap` follows.

Compared with the approximate-table route, the only open compiler obligation
is now to preserve a fixed finite family of **normal-generation relation
words**.  Arbitrary A8 multiplication checks and all unused group states have
been eliminated from the proof portfolio.
