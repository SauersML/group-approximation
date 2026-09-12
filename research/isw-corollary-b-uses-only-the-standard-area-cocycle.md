---
rg: 2
id: isw-corollary-b-uses-only-the-standard-area-cocycle
kind: claim
title: Ioana--Spaas--Wiersma Corollary B runs on the standard action and its area form, which the Siegel module does not carry
distinct_from:
  sp4-maximal-parabolics-contain-no-isw-affine-subgroup: that shows the proved obstruction GROUP Z^2 x| F does not embed in either parabolic; this pins down, at the level of the ISW text, the MECHANISM of their Corollary B (the invariant area cocycle of the standard module) and verifies the Siegel symmetric-square module has no such form at all.
  isw-scalar-cocycle-obstruction-dies-on-sp4-parabolic-radicals: that bounds the Levi-invariant scalar H^2 of the radicals; this is the source-level scope audit of Corollary B itself, including its co-induction clause.
---

Source-verified 2026-08-21 against arXiv:2006.01874 (pp. 2, 11-12).

**(i) Scope of Corollary B.**  The corollary covers exactly:
`Gamma = Z^2 x| Sigma` for non-amenable `Sigma < SL_2(Z)` (standard
action), hence `C^*(Z^2 x| SL_2(Z))` and `C^*(SL_n(Z))`, `n >= 3`;
more generally `C^*(R^2 x| SL_2(R))` and `C^*(SL_n(R))` for a finitely
generated commutative unital ring with `{2x : x in R}` infinite; and a
"moreover" clause for any countable group containing `F_2`, obtained by
CO-INDUCTION from the standard `Z^2` action (their p. 12, citing the
proof of Proposition 4.5 of [Io11]).  Every clause is built on the
STANDARD rank-two module.

**(ii) The engine cocycle.**  The proof (their Sections 3.2, pp. 11-12)
takes the `SL_2`-invariant integral area form `c((x,y),(z,t)) = xt - yz`
on the standard module, extends it to the semidirect product by
invariance (`c((a,g),(b,h)) = c(a, g.b)`), sets
`c_k = exp(2 pi i c / k)` (general `R`: composes with characters
`phi_k -> 1` chosen via residual finiteness of `R`), and realizes `c_k`
in finite dimensions because `c_k` factors through the FINITE quotient
`(Z/k)^2 x| SL_2(Z/k)` (resp. `(R/I_k)^2 x| SL_2(R/I_k)`), whose
twisted regular representation is finite-dimensional.  Both
non-coboundarity (`c_k` restricted to the module is non-symmetric) and
pointwise triviality (`1/k -> 0`) are read off this one invariant form.

**(iii) The Siegel module carries no such form.**  The Siegel pair of
`Sp_4(Z)` has module `Sym^2(Z^2) = Z^3` with `GL_2(Z)` acting by the
symmetric square.  There is NO nonzero alternating bilinear form on
`Sym^2(Q^2)` invariant under even the two integral unipotents of
`SL_2(Z)`.  Hand computation: in the basis `(e^2, ef, f^2)` the
unipotent `u: e -> e, f -> e + f` acts by the matrix
`U = [[1,1,1],[0,1,2],[0,0,1]]` and `l: e -> e + f, f -> f` by
`L = [[1,0,0],[2,1,0],[1,1,1]]`; for the general alternating form
`B(x,y) = p(x_1y_2 - x_2y_1) + q(x_1y_3 - x_3y_1) + r(x_2y_3 - x_3y_2)`,
the condition `U^T M U = M` on the Gram matrix forces `p = q = 0`, and
then `L^T M L = M` forces `r = 0`.  So no ISW-type invariant area
cocycle exists on the Siegel module, and the Corollary B recipe has no
Siegel analogue.  (This is the source-level confirmation of the
"no rational invariant line" step recorded in
`isw-scalar-cocycle-obstruction-dies-on-sp4-parabolic-radicals`.)

**Remark.**  Independently of (iii), the global Siegel-pair extension
program (finding `Sp_4(Z)`-cocycles restricting nontrivially to the
Siegel module) is dead by `isw-theorem-a-has-no-data-on-sp4-lattice`.
