---
rg: 2
id: hs-block-decomposition-from-stable-branch
kind: route
title: On the stable branch every almost-representation collapses and rank-one atoms give the decomposition
target: hs-expander-block-decomposition
requires: [leavitt-steinberg-hs-stable, stable-branch-trivializes-hs-block-programme]
---

`stable-branch-trivializes-hs-block-programme`, item 2, is exactly this
implication.  On the stable branch, every almost-representation of
`G = EL_D(R)` is uniformly close to `1`, and any rank-one basis decomposition
satisfies all clauses with `eps(delta) = 4 eta(delta)^2`.

**Why a cycle is written deliberately.**
`hs-blocks-select-stable-branch-through-masa-transport` proves the opposite
implication.  The pair of routes records that this frontier hole is
*equivalent* to `leavitt-steinberg-hs-stable`, not a decomposition of it.
`cairn check` warns about the dependency cycle.  The least fixpoint never
fires on it, so neither claim can establish itself.  Do not delete either
implication to silence the warning: both are proved.
