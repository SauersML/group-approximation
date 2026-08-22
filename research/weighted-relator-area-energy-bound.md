---
rg: 2
id: weighted-relator-area-energy-bound
kind: claim
title: A relator sampling law converts multiplicity area into an exact HS energy denominator
distinct_from:
  hs-dehn-modulus-bounded-by-dehn-function: that bounds a word defect by unweighted van Kampen area times the maximum relator defect; this optimizes against an arbitrary relator sampling distribution and records the sharp Cauchy--Schwarz denominator.
  bounded-overlap-syndrome-energy-accounting: that sums local lower payment inequalities with bounded overlap; this starts from one explicit identity-word decomposition and derives its global sampled-energy lower bound directly.
---

ESTABLISHED.
Let a word `w` have a free-group identity decomposition as conjugates of
defining relators, and let `m_r` be the number of occurrences of relator
type `r` (either orientation).  For positive sampling weights `p_r` with
`sum_r p_r=1`, put

```text
E_p(U)=sum_r p_r||r(U)-1||_2^2.                               (WAE1)
```

Every unitary tuple satisfies

```text
||w(U)-1||_2^2
 <= E_p(U) sum_r m_r^2/p_r.                                  (WAE2)
```

Thus a maximally separated involutory mark, for which
`||w(U)-1||_2=2`, forces

```text
E_p(U)>=4/(sum_r m_r^2/p_r).                                 (WAE3)
```

The denominator, rather than raw area alone, is the exact obstruction to a
weighted proof menu.  Optimizing the sampling law gives `p_r` proportional
to `m_r` and recovers the ordinary square-area loss
`4/(sum_r m_r)^2`; nonuniform sampling cannot beat that value for one fixed
diagram.
