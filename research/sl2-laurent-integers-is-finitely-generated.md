---
rg: 2
id: sl2-laurent-integers-is-finitely-generated
kind: claim
title: "SL_2(Z[t,t^-1]) is finitely generated"
---

The group `SL_2(Z[t,t^{-1}])` of 2×2 integral Laurent-polynomial matrices of
determinant 1 is finitely generated. This is the affirmative answer to Zaremsky
Problem 3.3 (`zaremsky-3-03-sl2-z-t-t-inverse-finitely-generated`).

By `sl2-laurent-integers-fg-iff-gamma0-t-in-fg-subgroup`, it is equivalent to: there
is a finite set `F` with `SL_2(Z[t]) ⊂ <E_2(Z[t,t^{-1}]) ∪ F>`.

## Attempts

- **Elementary generation.** If `SL_2(Z[t,t^{-1}]) = E_2(Z[t,t^{-1}])`, the answer is
  yes, since `E_2` is finitely generated; route
  `sl2-laurent-integers-fg-via-elementary-generation`, open input
  `sl2-laurent-integers-equals-elementary-subgroup` (unknown per the zbMATH review of
  Knudson 2008).
- **Product of trees.** `SL_2(Z[t,t^{-1}])` acts on `T_0 × T_∞` (Bruhat–Tits trees of
  `Q((t))` and `Q((t^{-1}))`). The stabilizer of the base vertex is `SL_2(Z)`, and the
  vertex stabilizers are arithmetic groups. The quotient is not compact: the
  stabilizer `SL_2(Z[t])` of the base vertex of `T_0` has infinitely many orbits on
  `T_∞`, detected by the index `d` of `W ∩ Z[t]^2` in 2-dimensional `Q`-subspaces
  `W = gQ^2` (for `g = E_12(t/n)` one gets `d = n`). A yes answer by Brown's
  criterion needs a cocompact connected invariant subcomplex, e.g. sublevel sets of a
  Morse function bounding both cusp heights and this denominator invariant.
- **Caution (Krstić–McCool).** Any subgroup of `GL_2(R)` containing `E_2(R)` is not
  finitely presented, so a yes answer cannot come from a finite presentation.
