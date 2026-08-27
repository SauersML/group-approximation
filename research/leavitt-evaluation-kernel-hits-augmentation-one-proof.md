---
rg: 2
id: leavitt-evaluation-kernel-hits-augmentation-one-proof
kind: route
title: The Leavitt algebra has no character to F_2, twice
target: leavitt-evaluation-kernel-hits-augmentation-one
requires: [leavitt-unit-group-algebra-surjects-onto-leavitt]
artifacts:
  - research/artifacts/gottschalk-leavitt-audit-2026-08-17.md
---

## Why sufficient

*No unital ring homomorphism `phi : R -> F_2`.*  From `t_0 s_0 = 1`, both
`phi(t_0)` and `phi(s_0)` are nonzero in `F_2`, hence `1`.  From
`t_1 s_1 = 1`, likewise `phi(t_1) = phi(s_1) = 1`.  Then `t_0 s_1 = 0` reads
`1 = 0`, which is false in `F_2`.

*Part 1.*  The prerequisite gives that `pi` is onto.  If also `K = 0` then
`pi` is a ring isomorphism, and `eps . pi^(-1)` is such a `phi`.

*Part 2.*  If `eps(K) = 0` then `K` is contained in `ker(eps)`, so `eps`
factors through `S/K`, which `pi` identifies with `R` as a ring; the induced
map is again such a `phi`.  Hence `eps(K) != 0`, and since `F_2` has only the
two elements, `eps(K) = F_2`.

Both arguments use only that `F_2` is a nonzero commutative ring, so they
hold verbatim over any coefficient field.
