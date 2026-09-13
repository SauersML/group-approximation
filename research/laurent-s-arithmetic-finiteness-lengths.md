---
rg: 2
id: laurent-s-arithmetic-finiteness-lengths
kind: claim
title: SL_3(F_q[t,1/t]) is finitely presented, while SL_2(F_q[t,1/t]) and SL_3(F_q[t]) are finitely generated but not finitely presented (Rank Theorem)
distinct_from:
  elementary-groups-over-polynomial-s-integers-are-fp: that is the number-field-coefficient stable-range statement E_n(Z[1/m][t_1..t_k]) f.p. for n >= k+4; this is the positive-characteristic S-arithmetic finiteness length for the Laurent and polynomial Hecke hosts
  polynomial-gl2-over-a-field-is-a-nontrivial-amalgam: that is Nagao's amalgam, which shows SL_2(F_q[t]) is not finitely generated; this records the finiteness lengths of the neighbouring hosts through the Rank Theorem
---

**ESTABLISHED** (literature import; route
`laurent-s-arithmetic-finiteness-lengths-citation`).

Let `q` be a prime power and `K=F_q(t)`.  For `S={t=0,t=infinity}` the
`S`-integers are `F_q[t,1/t]`; for `S={t=infinity}` they are `F_q[t]`.  With
`d` the sum over `S` of the local ranks and finiteness length `d-1`:

```text
group            S          d    finiteness
SL_3(F_q[t,1/t]) {0,inf}    4    type F_3, finitely presented
SL_2(F_q[t,1/t]) {0,inf}    2    type F_1: finitely generated, not finitely presented
SL_3(F_q[t])     {inf}      2    finitely generated, not finitely presented
SL_2(F_q[t])     {inf}      1    not finitely generated
```

Consumers.
- Item 5 of `sofic-coset-actions-pass-to-marked-colimits` applies to the
  rank-two Hecke pair `SL_3(F_2[t]) < SL_3(F_2[t,1/t])`: the host is finitely
  presented and the Kazhdan stabilizer is finitely generated.
- It does not apply to the rank-one pair
  `SL_2(F_2[t]) < SL_2(F_2[t,1/t])`: the host is not finitely presented and
  the stabilizer is not finitely generated.
