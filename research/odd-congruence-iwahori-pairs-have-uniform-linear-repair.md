---
rg: 2
id: odd-congruence-iwahori-pairs-have-uniform-linear-repair
kind: claim
title: Exact odd-congruence Iwahori pairs admit uniform linear compatible repair
distinct_from:
  iwahori-local-global-defect-question: that asks for one modulus on all finite-dimensional modular vertex representations; this proves a linear modulus only when both vertices already factor through odd congruence quotients, with no bound on either level.
  odd-congruence-vertex-sector-admits-no-exact-leak: that excludes one ultraproduct commutant leak after a single vertex has been exactified; this directly repairs two finite-dimensional vertex representations to an exactly compatible pair.
  iwahori-fractional-transport-integralization: that asks for physical block integralization for arbitrary edge types; here odd-level edge fullness makes every edge-reducing projection automatically reduce its whole modular vertex.
---

Let `C_+,C_-` be the two copies of `SL_2(Z)`, let `B_+`,`B_-` be
the opposite index-three Iwahori subgroups, and let
`sigma:B_+->B_-` be the Dogon--Vigdorovich commensuration.  Fix the
standard edge generating set `S_B`.  There are constants `kappa>0` and
`K<=10/kappa`, independent of dimension and congruence levels, with the
following property.

Suppose

```text
pi_+:C_+->U(d),                 pi_-:C_->U(d)
```

are exact representations, each factoring through an odd congruence
quotient (the two levels may differ), and put

```text
epsilon=max_(s in S_B)||pi_+(s)-pi_-(sigma(s))||_2.       (OCR1)
```

Then there are exact vertex representations `pi~_+`,`pi~_-` in the same
dimension such that

```text
pi~_+(b)=pi~_-(sigma(b))                   (b in B_+),    (OCR2)
max_(g in S_+ union S_-)||pi_g-pi~_g||_2 <= K epsilon.   (OCR3)
```

Thus the Dogon--Vigdorovich agreement problem has a uniform **linear**
positive answer on the entire exact odd-congruence sector, even when the
levels grow.  Any counterexample after vertex exactification must retain an
essential two-primary or noncongruence vertex component; deterioration of
constants along odd levels cannot be the obstruction.

