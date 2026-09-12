---
rg: 2
id: residually-nilpotent-implies-lef-proof
kind: route
title: Pass to the finitely generated subgroup, then Hirsch
target: residually-nilpotent-implies-lef
requires: []
---

## Why sufficient

Three steps, each standard on its own; the content is only that they compose
without a finite generation hypothesis on the ambient group.

**Residual nilpotence is subgroup-closed.**  Let `G` be residually nilpotent and
`H <= G`.  For `h in H` with `h != 1`, residual nilpotence of `G` gives
`phi: G -> Q` with `Q` nilpotent and `phi(h) != 1`.  Restricting, `phi|_H` maps
`H` into `Q`; its image is a subgroup of a nilpotent group, hence nilpotent, and
still separates `h` from `1`.

**Finitely generated plus residually nilpotent implies residually finite.**  Let
`H` be finitely generated and residually nilpotent, and `h != 1` in `H`.  Take
`phi: H -> Q` nilpotent with `phi(h) != 1`.  Replace `Q` by `phi(H)`, which is
finitely generated, being the image of a finitely generated group, and still
nilpotent.  A finitely generated nilpotent group is polycyclic and therefore
residually finite (Hirsch).  So some finite quotient `phi(H) -> F` keeps the
image of `h` nontrivial, and the composite `H -> F` separates `h` from `1`.

**LEF is local.**  Let `G` be residually nilpotent and `S subset G` finite.  Put
`H = <S>`, which is finitely generated, and residually nilpotent by the first
step, hence residually finite by the second.  Residual finiteness gives LEF
(Vershik--Gordon): a finite quotient separating the finitely many nontrivial
elements of `S . S` restricts to a multiplicative embedding of `S` into a finite
group.  Since `S` was an arbitrary finite subset of `G`, `G` is LEF.

## Scope

The argument uses nothing about `G` beyond residual nilpotence, so it applies
verbatim to uncountable groups.  It does not extend to residual solvability:
finitely generated solvable groups need not be residually finite, so the second
step fails there, and indeed residually solvable non-LEF groups are not excluded
by this argument.
