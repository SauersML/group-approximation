---
rg: 2
id: klingen-center-kills-isw-condition-one-proof
kind: route
title: Central extensions of a free group split by sending the generator anywhere above itself
target: klingen-center-kills-isw-condition-one
requires: []
---

Let `c in Z^2(Z,T)`.  It defines a central extension
`1 -> T -> E -> Z -> 1` with `E = T x Z` as a set and multiplication
twisted by `c`.  Choose any `e in E` mapping to the generator
`1 in Z`.  Since `Z` is free (on one generator), `n -> e^n` is a
well-defined group homomorphism `Z -> E` splitting the extension.  A
central extension with a splitting has cohomologous-to-trivial cocycle:
explicitly, writing `e^n = (beta(n), n)`, the 2-cocycle identity for
the section `n -> (beta(n), n)` gives
`c(m,n) = beta(m) + beta(n) - beta(m+n)` (additive notation in `T`),
i.e. `c = delta(beta)` is a coboundary.  Hence `H^2(Z,T) = 0`, which
is `(KC1)`; hypothesis (1) of Ioana--Spaas--Wiersma Theorem A
(arXiv:2006.01874, p. 2: "the restriction of `c_n` to `Lambda` is not
a 2-coboundary, for every `n`", source-verified 2026-08-21) can never
hold for an infinite cyclic `Lambda`.

The Klingen identifications (`H_3(Z)` radical, `SL_2(Z)` Levi acting
standardly on `H_3(Z)/Z(H_3(Z)) = Z^2` and fixing the center) are as
recorded in `sp4-maximal-parabolics-contain-no-isw-affine-subgroup`
(SPF2).  The relative property (T) remark is the Kazhdan--Margulis
definition quoted by ISW (p. 2): a unitary representation of `Gamma`
with almost invariant vectors has a nonzero invariant vector when
`Gamma = Sp_4(Z)` is Kazhdan, and an invariant vector is in particular
`Lambda`-invariant for every `Lambda`.
