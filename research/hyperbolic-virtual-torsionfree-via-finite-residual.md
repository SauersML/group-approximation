---
rg: 2
id: hyperbolic-virtual-torsionfree-via-finite-residual
kind: route
title: Reduce virtual torsion-freeness to torsion in the finite residual
target: hyperbolic-groups-virtually-torsion-free
requires:
  - finite-torsion-carrier-virtual-torsionfree-criterion
  - hyperbolic-finite-residual-is-torsion-free
artifacts:
  - research/artifacts/luck-2008-section-11-status-and-finite-torsion-test-2026-08-30.md
---

For a word-hyperbolic group `G`, there are only finitely many conjugacy
classes of finite subgroups.  Choose representatives `F_1,...,F_r`; every
finite subgroup is then conjugate to, and in particular conjugate into, one
of them.  The finite torsion-carrier criterion applies and gives

```text
G virtually torsion-free
  <=> R_f(G) torsion-free
  <=> some finite quotient of G is injective on every F_i.
```

Consequently `hyperbolic-finite-residual-is-torsion-free` proves the target.
Conversely the target itself implies that claim, by taking the normal core
of a torsion-free finite-index subgroup.  The route is therefore an exact
reformulation, not merely a sufficient condition.

The distinction from residual finiteness is sharp: the criterion permits an
arbitrary torsion-free finite residual.  Any counterexample to the target,
on the other hand, must exhibit a specific finite-order element invisible in
every finite quotient.
