---
rg: 2
id: iwahori-question-as-square-root-of-parabolic
kind: claim
title: PSL2(Z[1/2]) is two copies of C2 star C3 glued by squaring the parabolic and matching one involution
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
  - experiments/psl2_presentation_check.py
distinct_from:
  iwahori-local-global-defect-question: that is Dogon--Vigdorovich's question in representation-variety language; this is an explicit, numerically verified finite presentation and an equivalent square-root formulation of the same question.
  parabolic-spectrum-is-doubling-invariant: that is the spectral constraint from the single element diag(2,1/2); this is the full amalgam presentation and its square-root reformulation.
---

Write `PSL_2(Z) = C_2 * C_3 = <x, y | x^2, y^3>` with `x = S = [[0,-1],[1,0]]`
and `y = ST = [[0,-1],[1,1]]` (order 3).  Then the parabolic is `T = xy =
[[1,1],[0,1]]`, and the Iwahori subgroup `B = Gamma_0(2)/{+-I}` (lower-left
even, index 3) is `<T, w>` with the involution

```text
w = x y^2 x y x = [[1,-1],[2,-1]]     (order 2 in PSL_2, since w^2 = -I),
```

so `B ~= Z * C_2` (the Dogon--Vigdorovich edge group).  With `V_1 = V_2 =
PSL_2(Z)` glued over `B_+ ~= B_-` by `sigma = ` conjugation by
`diag(sqrt 2, 1/sqrt 2)`, which acts as `sigma(T) = T^2` and
`sigma(w) = t w t^(-1) = [[1,-2],[1,-1]] = x y x y^2 x` (the mirror word),
Serre's tree decomposition gives

```text
PSL_2(Z[1/2]) = < x, y, x', y' |  x^2 = y^3 = x'^2 = y'^3 = 1,
                                  x y = (x' y')^2,               (T = T'^2)
                                  x y^2 x y x = x' y' x' y'^2 x' >.  (w = sigma-word)   (SR1)
```

**This presentation is numerically verified**
(`experiments/psl2_presentation_check.py`): for the permutation
representation of `PSL_2(F_p)` on `P^1(F_p)` with the second copy taken as
`t^(-1) PSL_2(Z) t`, all four torsion relations and both gluing relations
hold to machine precision for `p = 3, 5, 7, 11, 13, 17, 23`, and the
parabolic `T = xy` has odd order exactly `p`.  (An earlier version of this
node used the non-Iwahori element `V = xy^2` in the second relation and the
un-mirrored word; both are corrected here -- the test exposed the error, as
`xy^2 = [[1,0],[1,1]]` has odd lower-left entry and so is not in
`Gamma_0(2)`.)

**Square-root form of the gluing.**  A representation of `PSL_2(Z[1/2])` is
a representation `(x, y)` of `PSL_2(Z)` together with a second one
`(x', y')` whose parabolic `T' = x' y'` is a **square root** of `T = xy`
(`T'^2 = T`) and whose involution matches the mirror word `(SR1)`.  In a
congruence representation `T` has odd order `m`, and `T' = ` the
`PSL_2(Z)`-parabolic of odd order `2m` with `T'^2 = T` (equivalently
`T' = T^((m+1)/2)` inside `<T>` only if that lies in a genuine second
`PSL_2(Z)`-representation -- which is exactly the arithmetic content).  So
Dogon--Vigdorovich's question is: for an exact representation `(x, y)` of
`PSL_2(Z)` and an approximate compatible second copy, is the pair close to
a congruence representation with its canonical square root?

**Sanity/bug-catching.**  A gradient search minimizing the two gluing
defects of the *incorrect* earlier presentation found spurious exact
solutions with non-atomic parabolic spectrum; those disappeared once the
presentation was corrected to `(SR1)`, which is the value of keeping the
numerical check in the loop.
