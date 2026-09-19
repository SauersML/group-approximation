---
rg: 2
id: independent-finite-clocks-round-to-arbitrary-row-pvms
kind: claim
title: Independent finite clocks round to arbitrary-multiplicity row PVMs on one marked corner
artifacts:
  - research/artifacts/independent-set-rounding-rank-router-2026-08-23.md
distinct_from:
  finite-clock-fejer-threshold-is-sharp: that bounds fixed-frequency return mass; this compresses a complete clock spectrum and rounds every outcome simultaneously.
  exhaustive-marked-type-energy-summation: that sums central isotypic pieces of one packet; independent clocks impose no common spectrum or multiplicity profile across questions.
---

**ESTABLISHED.**  Let `Q` be a projection and let

```text
U^N=1,                   U=sum_v lambda_v E_v,
a_v=QE_vQ.
```

Put `Delta_N=2sin(pi/N)`.  The compressed effects form an exact POVM in
`QMQ`, and their purity deficit obeys

```text
D_Q=tau(Q)-sum_v tau(a_v^2)
   =sum_(v!=w)||E_vQE_w||_2^2
   <=Delta_N^(-2)||[Q,U]||_2^2.                       (FCR1)
```

There is therefore a genuine PVM `(p_v)` summing to `Q` with

```text
sum_v||QE_vQ-p_v||_2^2
 <=9Delta_N^(-2)||[Q,U]||_2^2.                        (FCR2)
```

One independent clock `U_i` per game question gives arbitrary outcome
multiplicities.  In an approximate group model, fixed-`N` spectral rounding
and the commutator of `U_i` with the marked involution control `(FCR2)` with
a dimension-independent modulus.

