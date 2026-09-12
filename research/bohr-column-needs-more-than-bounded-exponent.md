---
rg: 2
id: bohr-column-needs-more-than-bounded-exponent
kind: claim
title: The torsion shortcut to the Bohr column does not close it
artifacts:
  - GroupApproximation/Sofic/AlternatingLampBohrResidual.lean
  - research/artifacts/invisible-quotients-architecture-audit-2026-08-23.md
---

The lamp subgroup `A_n^(X)` is torsion of bounded exponent -- an element is a
finitely supported configuration, so its order divides `exp(A_n)`.  That
suggests a route to `A_n^(X) <= Rad_Bohr(W_n)` avoiding Peter--Weyl entirely,
via the classical statement that a compact Hausdorff group of finite exponent is
totally disconnected.  **The route does not close.**

The unconditional part is real.  For any `f : W_n -> C` with `C` compact
Hausdorff, put `N = closure (f '' A_n^(X))`.  Then `N` has exponent dividing
`exp(A_n)`: the set `{x : x^e = 1}` is the preimage of the closed set `{1}`
under the continuous `e`-th power map, it contains `f '' A_n^(X)`, so it
contains the closure.  `N` is a closed subgroup of a compact group, hence a
compact Hausdorff group of finite exponent.

**Where it breaks.**  Granting the finite-exponent statement makes `N`
profinite -- and a subgroup of a profinite group is not thereby trivial, which
is what the argument needs.  The only lever that gives triviality is
`Res_fin(W_n) = A_n^(X)`: a finite quotient separating `f x` pulls back to a
finite-index subgroup of `W_n` missing `x`, contradicting `x` in the finite
residual.  That lever requires a finite quotient of `closure (f '' W_n)`, not of
`N`.  And `closure (f '' W_n)` has no bounded exponent -- the acting group `V`
is torsion-free-by-arithmetic, not torsion -- so the finite-exponent statement
says nothing about it.

**What is actually needed.**  Separation for the full image, which is
Peter--Weyl.  Nor can the family's own collapse be transported: in `W_n` the
lamp at a site does *not* commute with all of its conjugates (the stabilizer of
the site acts nontrivially on that site's copy of `A_n`), so the commuting
hypothesis of the purely algebraic `eq_one_of_commuting_image_of_perfect` is
supplied by the corona-specific spectral collapse and by nothing else.  A
compact target offers the algebraic half without the analytic one.

Recorded because the shortcut is attractive, cheap to re-invent, and wrong for a
reason that is invisible until the final step.
