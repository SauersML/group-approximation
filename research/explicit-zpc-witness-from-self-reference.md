---
rg: 2
id: explicit-zpc-witness-from-self-reference
kind: route
title: Freeze the effective self-referential gap game into a literal explicit witness
target: explicit-zpc-irs-gap-game-witness
requires:
  - self-referential-perfect-zpc-irs-gap
  - materialize-self-referential-zpc-game
---

The first prerequisite identifies one particular TailoredMIP fixed-point
instance `e_*` and proves for its finite game `G_*` that

```text
omega_ZIRS(G_*)=1,
omega*(G_*)<1/2,
```

with the value one attained by an actual ZPC-IRS strategy.  The second
prerequisite writes that already-specified finite game out as canonical
repository data and checks that it is the compiler output for `e_*`.
Together these are exactly the requested explicit witness: a fully specified
finite game plus a proof certificate for perfect ZPC-IRS completeness and the
strict quantum soundness gap.

The point of this route is that explicitness is no longer a search problem.
Before the self-reference argument, the undecidability proof only said that
*some* nonhalting machine had the desired perfect IRS value.  Now the source
machine is fixed effectively; the only remaining work on this branch is
finite syntactic materialization.
