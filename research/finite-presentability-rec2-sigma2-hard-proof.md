---
rg: 2
id: finite-presentability-rec2-sigma2-hard-proof
kind: route
title: Bieri--Strebel forbids an ascending HNN structure over a finitely generated subgroup of the shift right-angled Artin kernel
target: finite-presentability-two-generator-recursive-is-sigma2-hard
requires:
  - shift-raag-family-classifies-amenability
---

If `J` is finite, `G_J` is finitely presented by definition.  Suppose `J`
is infinite and `G_J` were finitely presented.  `G_J = N x| <t>` with
`N = A(Gamma_J)` (see [[shift-raag-family-classifies-amenability]]), and
`N` is not finitely generated: its abelianization is free abelian on the
infinitely many vertices `a_i`.  By the Bieri--Strebel theorem (a
finitely presented group with an epimorphism to `Z` whose kernel is not
finitely generated is an ascending HNN extension of a finitely generated
subgroup `B` of the kernel, with stable letter `t` or `t^-1`), there is a
finitely generated `B <= N` with `t^{e} B t^{-e} <= B` and
`N = U_k t^{-ek} B t^{ek}` for some `e in {+-1}`.  A finitely generated
subgroup of `A(Gamma_J)` lies in the parabolic subgroup on a finite window
`{a_i : |i| <= r}`; conjugating by `t^{-ek}` shifts the window by `-ek`,
so the union of the shifted windows misses every `a_i` with `ei > r`,
which lie in `N` but not in the union.  Contradiction.  So `G_J` is not
finitely presentable.

For hardness use `J_e = {1, ..., |W_e|}`: `G_{J_e}` is finitely
presentable iff `W_e` is finite, and `FIN` is `Sigma^0_2`-complete.

Upper bound: for a recursive presentation `<X | r_1, r_2, ...>`, finite
presentability of the group is equivalent to the existence of `m` such
that every `r_j` lies in the normal closure of `r_1, ..., r_m`
(a finitely presented group has, for every presentation on the same
finite generating set, a finite subset of the relators that suffices,
since the finitely many relators of some finite presentation are
consequences of finitely many `r_j`, and conversely).  "`r_j` lies in the
normal closure" is `Sigma^0_1`, so the whole is
`exists m forall j exists`: `Sigma^0_3`.
