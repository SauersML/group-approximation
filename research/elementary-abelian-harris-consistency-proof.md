---
rg: 2
id: elementary-abelian-harris-consistency-proof
kind: route
title: Complete each Boolean PVM by translations and compare overlap differences
target: elementary-abelian-harris-lift-compiles-bcs-consistency
requires:
  - harris-bisynchronous-game-algebra-preservation
  - finite-phase-monomial-game-algebra-dictionary
---

For fixed `(r,c)`, translation `a |-> a-r` permutes `V`, so the corresponding
column in `(EAH1)` sums to one; the same argument with `r |-> a-r` gives every
row sum.  PVM orthogonality gives magic-unitary orthogonality.  The inverse
formula for `e_(x,c)` proves that no generators are lost.

Over `F_2`, the equality of decoded overlap assignments is

```text
pi_(cd)(a-r)=pi_(cd)(b-s)
 iff pi_(cd)(r-s)=pi_(cd)(a-b),
```

which is exactly equality of a source-pair and target-pair color.  Finally,
the translations `(EAH3)` preserve all pair differences.  Choosing a global
assignment which violates a local predicate proves that pair colors alone do
not impose the omitted zero projection.  Distinct scalar labels are used;
for finite `s` they must represent distinct `mu_s`-orbits, not merely
different roots of unity.
