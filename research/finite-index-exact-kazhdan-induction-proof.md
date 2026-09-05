---
rg: 2
id: finite-index-exact-kazhdan-induction-proof
kind: route
title: Induce the exact subgroup representation and round its almost-invariant range projection
target: subgroup-exact-outliers-do-not-exist
requires:
  - moving-subgroup-schreier-correction-has-no-index-loss
---

Fix a transversal of the subgroup in the target, without replacing it by
its normal core.  Set `V_t=sigma_j(q_t)` on the finitely many section
representatives.  Express every Schreier element `n(s,t)` in the fixed
subgroup generating menu on which `pi_j` is close to `sigma_j`.

The section identities have a finite root-mean-square area bound `B`, and
the subgroup expressions have a finite root-mean-square length bound `L`.
Both are independent of `j` because the subgroup and all word choices are
fixed.  Thus `(MSC3)` in the required theorem gives

```text
beta_j <= B delta_j+L xi_j -> 0.
```

Apply `(MSC2)`.  It gives exact representations on dimensions `D_j>=d_j`
with `D_j/d_j<=1+4beta_j^2/kappa^2` and generatorwise distance at most
`(1+10/kappa)beta_j` from the padded original tuple.  This is the target's
flexible normalized-HS correction.  The quantitative theorem additionally
shows that only the actual word ledger, not the index itself, matters if
one later allows the subgroup to move.
