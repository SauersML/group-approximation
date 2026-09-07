---
rg: 2
id: deligne-sep7-norm-parameter-closed-subgroup
kind: claim
title: Point-norm Maslov parameters form a closed subgroup containing the metaplectic half parameter
artifacts:
  - research/artifacts/deligne-sep7-all-cover-mf-classification.md
distinct_from:
  maslov-ce-parameter-set-is-a-closed-subgroup: that concerns canonical tracial microstates; this concerns pointwise operator-norm projective models without a trace or separation requirement.
  deligne-maslov-opnorm-sector-is-mf-quotient: that identifies the two mod-three sectors with nonzero MF quotients; this treats all parameters and proves their subgroup and closure structure.
---

Fix a normalized integral cocycle `b` representing the actual universal-cover
extension of `Gamma=Sp_4(Z)`, and put

```text
c_theta(g,h)=exp(2 pi i theta b(g,h)),   theta in R/Z.
```

Let `P_op` consist of those parameters for which there are positive integers
`d_n` and maps `U_n:Gamma->U(d_n)`, with `U_n(e)=I`, satisfying

```text
||U_n(g)U_n(h)-c_theta(g,h)U_n(gh)||_op -> 0
```

for every fixed pair `g,h`. No separation or prescribed trace is required.
Then `P_op` is a closed subgroup of `R/Z` containing `1/2`. Consequently
either `P_op=R/Z`, or `P_op=(1/m)Z/Z` for one positive even integer `m`.

The choice of `b` is the integral covering cocycle itself; an unnormalized
Meyer cocycle multiplied by four is not interchangeable at all denominators.

The result does not decide whether `1/3` belongs to `P_op`.
