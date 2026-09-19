---
rg: 2
id: algebraic-selector-mixing-frame-collapse-proof
kind: route
title: Compress the universal frame by the forbidden source projection
target: algebraic-selector-mixing-frame-collapses-forbidden-sector
requires: []
---

Compress `(ASM3)` on both sides by `F=Q(1-p)`.  Since `F<=Q`,

```text
kappa F
 <=sum_i F S_i^*q_iS_i F
 =sum_i (q_iS_iF)^*(q_iS_iF).                         (AMP1)
```

But `q_i<=p_i`, `(ASM4)`, and `pF=0` give

```text
q_iS_iF
 =q_ip_iS_iF
 =q_iS_ipF
 =0.                                                    (AMP2)
```

The right side of `(AMP1)` is therefore zero.  Since `kappa>0` and `F` is a
projection, `F=0`, proving `(ASM5)`.

If a finite marked selector packet embeds, its group algebra embeds in
`C^*(Gamma)`.  Every nonzero character projection in that finite-dimensional
algebra remains nonzero.  In particular a forbidden atom below `Q(1-p)`
cannot satisfy `(ASM5)`.  Hence at least one of packet embedding, the
algebraic frame, or exact selector mixing must fail.

