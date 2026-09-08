---
rg: 2
id: deligne-sep8-first-order-tensor-threshold
kind: claim
title: Sublinear small-parameter projective defects force every finite Deligne cover to be MF
artifacts:
  - research/artifacts/deligne-sep8-first-order-tensor-threshold.md
distinct_from:
  deligne-sep7-norm-parameter-closed-subgroup: that starts with actual point-norm models at each parameter; this permits one imperfect tuple at each moving parameter and identifies the necessary error scale before tensor amplification.
  deligne-sep7-all-cover-mf-radical-classification: that classifies the possible finite-cover radicals; this supplies an equivalent perturbative criterion for the all-MF branch and a linear finite-window obstruction in the other branch.
---

Use the actual integral covering cocycle `b` and the parameter set `P_op`
from `deligne-sep7-norm-parameter-closed-subgroup`. The following are
equivalent:

1. Every finite Deligne cover `E_q` is MF.
2. `P_op=R/Z`.
3. There are nonzero real numbers `t_n->0` and maps
   `U_n:Sp_4(Z)->U(d_n)`, with `U_n(e)=I`, such that, for every fixed pair,

   ```text
   ||U_n(g)U_n(h)-exp(2 pi i t_n b(g,h))U_n(gh)||_op
       = o(|t_n|).
   ```

In particular an `O(t_n^2)` construction would make every finite cover MF
and refute the proposed nonzero MF radical of `E_3`. Merely obtaining
`O(|t_n|)` gives no such conclusion: the identity scalar tuple already has
that error on every fixed multiplication window.

There is also an explicit opposite implication. For a finite window `W`,
write `f_W(t)` for the infimum of its maximal projective operator defect
over all positive matrix sizes, and set `L=2 pi max_W |b(g,h)|`. If
`f_W(a)>=epsilon>0` for `0<a<=1/2`, then

```text
f_W(t) >= (epsilon/(2a)) |t|
```

whenever `0<|t|<=min(a,epsilon/(2L))`. Consequently the desired E3 gap
at `a=1/3`, if established, forces a fixed-window lower bound
`f_W(t)>=(3 epsilon/2)|t|` near zero.

This theorem supplies neither an `o(|t_n|)` construction nor a positive
gap. The exact E3 radical therefore remains unresolved.
