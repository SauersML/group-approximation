---
rg: 2
id: regularized-anchor-square-function-cut-proof
kind: route
title: Average the odd squares before spectral coarea
target: regularized-anchor-square-function-has-dimension-free-cut
requires:
  - covariant-square-function-has-common-reducing-threshold
  - one-anchor-odd-spike-has-a-cheap-reducing-cut
---

Each `R_(a,i)` is a positive contraction and commutes with `Q_a`, so the
same is true of their average `K_a`.  Also

```text
 tau(R_(a,i))=||[Q_a,Q_i]||_2^2/4,
```

which gives `(RAC2)`.  The direct covariance estimate `(OSC6)` gives, for
every `l`,

```text
 ||[K_a,Q_l]||_2
 <=(2/L)sum_i||[Q_i,Q_l]||_2+2||[Q_a,Q_l]||_2.
```

Average over `l` and apply Cauchy--Schwarz first to the full pair table and
then to the anchor row.  This proves `(RAC3)`.  Apply spectral coarea on
`[theta,2theta]` to `K_a`; Markov gives `(RAC4)`, coarea gives `(RAC5)`,
and functional calculus gives `(RAC6)`.  Since `p_a` commutes with the
anchor, the reset identity and `(RAC4)` give `(RAC7)`.  Finally
`E_a q_a^2=E_pair` and `E_a q_a<=sqrt(E_pair)`, proving `(RAC8)`.
