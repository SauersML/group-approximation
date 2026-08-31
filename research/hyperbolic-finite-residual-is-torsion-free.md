---
rg: 2
id: hyperbolic-finite-residual-is-torsion-free
kind: claim
title: The finite residual of every word-hyperbolic group is torsion-free
distinct_from:
  non-residually-finite-hyperbolic-group: that asks whether the finite residual is always trivial; this asks only whether it contains torsion and is exactly the weaker obstruction to virtual torsion-freeness
  finite-torsion-carrier-virtual-torsionfree-criterion: that is a proved abstract equivalence for groups whose torsion is carried by finitely many finite subgroups; this is the remaining open assertion after applying it to hyperbolic groups
artifacts:
  - research/artifacts/luck-2008-section-11-status-and-finite-torsion-test-2026-08-30.md
---

For every word-hyperbolic group `G`, prove that

```text
R_f(G) = intersection { ker(phi) : phi:G -> Q, Q finite }
```

contains no nonidentity element of finite order.

By `finite-torsion-carrier-virtual-torsionfree-criterion` and the standard
fact that a hyperbolic group has only finitely many conjugacy classes of
finite subgroups, this is equivalent to every hyperbolic group being
virtually torsion-free.  It is deliberately not strengthened to
`R_f(G)={1}`, which would be the still harder residual-finiteness problem.

## Attempts

- The finite-carrier theorem reduces the assertion to separating the finite
  set `union_i(F_i minus {1})` in finite quotients.  No known property of an
  arbitrary hyperbolic group supplies those quotients: invoking residual
  finiteness here would simply assume Lück 11.1(ii), a stronger open problem.
- `hyperbolic-prime-torsion-residual-dichotomy` shows it is enough to detect
  one representative of each prime-order subgroup.  It also proves that an
  undetected prime-order element is either central in the maximal finite
  normal subgroup or normally generates a non-elementary subgroup of the
  finite residual with full boundary.  This rules out small residuals when
  the finite radical is trivial, but neither remaining alternative is known
  to be impossible in general.
