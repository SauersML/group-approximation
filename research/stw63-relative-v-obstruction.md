---
rg: 2
id: stw63-relative-v-obstruction
kind: claim
title: Every LXIII counterexample is a relative projection-reflection failure
artifacts:
  - research/artifacts/stw63-z-embedding-audit-2026-08-30.md
---

If `phi,psi:Z->B` are not approximately unitarily equivalent, then for the
canonical inclusion of relative sequence algebras

```text
D = M_2(B_infinity) intersect diag(phi,psi)(Z)'
    ->
E = M_2((B**)_infinity) intersect diag(phi,psi)(Z)',    (1)
```

the two fixed corner projections `p=e_11` and `q=e_22` are inequivalent in
`D` but equivalent in `E`.  In particular, the induced map
`V(D)->V(E)` does not reflect equality on this pair.

Conversely, reflection of Murray--von Neumann equivalence for these two
corners, for every `B,phi,psi`, would prove LXIII.  This is an exact
obstruction, not a proposed invariant: it locates precisely what bidual
passage erases.
