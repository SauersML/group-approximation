---
rg: 2
id: stw09-summably-balanced-bratteli-models-give-af-embedding
kind: claim
title: Summably balanced Bratteli quasidiagonal models give a trace-preserving AF embedding
distinct_from:
  stw09-trace-preserving-af-embedding-iff-trace-coherent-models: that criterion requires traces on consecutive finite-dimensional stages to be exactly compatible; this theorem replaces exact compatibility by an explicit summable l1 defect in Bratteli weight vectors and proves that such an approximate trace thread shadows an exact one
  stw09-full-matrix-coherence-rational-core-criterion: that theorem obstructs coherence through full matrix stages by rational normalized ranks; this theorem permits arbitrary finite direct sums and arbitrary real trace weights, precisely the flexibility needed to avoid that obstruction
  stw08-af-embedding-iff-summably-coherent-fd-models: that is an untraced abstract coherence criterion; this theorem uses a faithful limiting trace for injectivity and gives finite multiplicity-matrix and weight-balance conditions which can be checked stage by stage
artifacts:
  - research/artifacts/stw09-summably-balanced-bratteli-model-audit-2026-08-30.md
---

Let `A` be a separable unital C-star algebra with faithful trace `tau`, and
fix a dense sequence `(a_l)` in its unit ball.  For every `n`, let

```text
F_n = direct_sum_(i=1)^(r_n) M_(d_(n,i))
```

and let `psi_n:A->F_n` be u.c.p.  Suppose the following data exist.

1. A nonnegative integer matrix
   `M_n=(m^(n)_(j i))_(j<=r_(n+1),i<=r_n)` satisfies

   ```text
   d_(n+1,j)=sum_i m^(n)_(j i)d_(n,i)                 (all j),
   sum_j m^(n)_(j i)>0                               (all i).
   ```

   Let `alpha_n:F_n->F_(n+1)` be the resulting unital embedding.

2. There are `epsilon_n>0` with `sum_n epsilon_n<infinity` such that

   ```text
   ||psi_(n+1)(a_l)-alpha_n(psi_n(a_l))|| <= epsilon_n
                                                              (l<=n).
   ```

3. The maps are asymptotically multiplicative on growing packets:

   ```text
   max_(l,k<=n)
   ||psi_n(a_l a_k)-psi_n(a_l)psi_n(a_k)|| -> 0.
   ```

4. There are probability vectors `w_n=(w_(n,i))_(i<=r_n)`.  Write

   ```text
   sigma_n = sum_i w_(n,i) tr_(d_(n,i)).
   ```

   Then `sigma_n psi_n(a)->tau(a)` for every `a in A`.

5. Define the Bratteli pullback of weights by

   ```text
   (P_n w_(n+1))_i
     = sum_j w_(n+1,j) m^(n)_(j i)d_(n,i)/d_(n+1,j).
   ```

   The trace-weight imbalance is summable:

   ```text
   sum_n ||w_n-P_n w_(n+1)||_1 < infinity.
   ```

Then there are a unital AF algebra `F`, a unital embedding `Phi:A->F`, and
a trace `sigma` on `F` such that `sigma Phi=tau`.

Thus exact trace balance at every Bratteli edge is unnecessary.  Summable
finite-dimensional weight imbalance suffices, and unlike full-matrix
coherence it permits irrational trace weights.
