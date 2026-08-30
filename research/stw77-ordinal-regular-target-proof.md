---
rg: 2
id: stw77-ordinal-regular-target-proof
kind: route
title: Use the properly infinite unit to eliminate quasitraces and invoke ordinal gluing
target: stw77-ordinal-regular-targets-solve-map
requires:
  - stw78-countable-ordinal-regular-targets
---

Suppose first that `B` admitted a normalized 2-quasitrace `tau`.  Proper
infiniteness of `1_B` supplies orthogonal projections `p,q<=1_B`, each
Murray--von Neumann equivalent to `1_B`.  A 2-quasitrace is invariant under
this equivalence and additive on the commuting orthogonal pair, so

```text
1=tau(1_B) >= tau(p+q)=tau(p)+tau(q)=2,
```

a contradiction.  Hence `B` has no normalized 2-quasitrace.

All remaining hypotheses of
`stw78-countable-ordinal-regular-targets` now hold.  That theorem glues
`O_infinity`-stability through the arbitrary ordinal filtration: at
countable-cofinality limits it uses sequential permanence, while at
uncountable-cofinality limits separability forces the filtration to have
stabilized.  It follows that `B` is `O_infinity`-stable and strongly purely
infinite.  Its nuclear-map conclusion makes the given `phi` strongly
`O_infinity`-stable.

Under the hypotheses of Problem LXXVII, `phi` is unital and every nonzero
positive element in its range is properly infinite.  Applying this to
`phi(1_A)=1_B` supplies the preceding unit hypothesis.  A map of finite
nuclear dimension is nuclear, so the original formulation is included.
