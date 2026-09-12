---
rg: 2
id: kaplansky-tester-via-subgroups-and-directed-colimits
kind: route
title: Combine subgroup heredity with finite-witness colimit arguments
target: kaplansky-three-properties-fixed-fp-torsion-free-tester
requires:
  - whitehead-universal-finitely-presented-torsion-free-group
  - torsion-free-directed-colimit-recursively-presented
---

Choose `U` from
[[whitehead-universal-finitely-presented-torsion-free-group]] and fix a field
`k`.

Each of the three properties is inherited by subgroups. If `H <= U`, then
`k[H] -> k[U]` is injective, so the assertions about zero divisors and
idempotents are immediate. If a two-sided unit `x in k[H]` is
`lambda u` in `k[U]`, uniqueness of support in the group basis forces
`u in H`, so the unit is already trivial in `k[H]`.

Now write an arbitrary torsion-free group as

```text
G = colim_i K_i
```

using [[torsion-free-directed-colimit-recursively-presented]]. Every `K_i`
embeds in `U`, although these embeddings need not be coherent. The group
ring functor `k[-]` preserves directed colimits.

All three bad behaviors have finite witnesses. A zero product of two nonzero
elements lifts to one stage and its equality to zero holds at a later common
stage; the lifts there stay nonzero because their colimit images are nonzero.
An idempotent and the equality `e^2=e` likewise occur at one stage. For a
unit, lift it together with a two-sided inverse and pass to a stage where both
product equalities hold. The corresponding property for `K_i`, inherited
from `U`, rules out the bad witness. Thus it holds for `G`.

The reverse implications use only that `U` is torsion-free. This argument
does **not** assert that every finitely generated torsion-free group embeds in
`U`; the directed-colimit step is essential. QED
