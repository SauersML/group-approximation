---
rg: 2
id: non-rf-kazhdan-weak-ucp-iff-proof
kind: route
title: Kazhdan averaging plus Malcev residual finiteness of finite-dimensional images, and a vacuous converse
target: non-rf-kazhdan-weak-ucp-iff-non-hyperlinear
requires:
  - kazhdan-almost-invariant-corner-near-invariant-projection
---

`(i) => (ii)`.  Apply weak ucp-stability to a hyperlinear approximation.
Its Stinespring corner is almost invariant, so
`kazhdan-almost-invariant-corner-near-invariant-projection` rounds it to a
finite-dimensional invariant corner of relative dimension `1+o(1)`, giving
the required flexible correction.  Conversely, a finite-dimensional
flexible correction is already a ucp dilation, so `(ii) => (i)`.

This equivalence concerns only hyperlinear approximations.  The stronger
claim that weak ucp-stability implies correction of **all** asymptotic
representations is
`kazhdan-weak-ucp-stability-is-flexible-stability` and additionally assumes
that `Gamma` is hyperlinear.  It cannot be invoked after assuming `(iii)`.

`(ii) => (iii)`.  Suppose `Gamma` is hyperlinear; then it admits a
hyperlinear approximation `phi_n : Gamma -> U(d_n)` (Dogon Def 1.4: this is
the definition of hyperlinearity in that language, Def 1.1).  By `(ii)`
there are genuine finite-dimensional unitary representations `rho_n` of
`Gamma` on `C^(D_n) supseteq C^(d_n)`, `D_n / d_n -> 1`, with
`|| phi_n(g) - P_n rho_n(g) P_n ||_(2,d_n) -> 0`.  For `g != e`,
`|| phi_n(g) - 1 ||_(2,d_n) -> sqrt 2`-or-more forces
`|| P_n rho_n(g) P_n - 1 ||_(2,d_n)` to stay bounded below, so
`rho_n(g) != 1` for large `n`.  Hence every nontrivial element of `Gamma`
is detected by a finite-dimensional unitary representation: `Gamma` is
maximally almost periodic.  A finitely generated subgroup of `U(D)` is
residually finite (Malcev), so the image `rho_n(Gamma)` is residually
finite and `rho_n(g) != 1` is detected by a finite quotient of that image,
hence by a finite quotient of `Gamma`.  Thus `Gamma` is residually finite,
contradicting the hypothesis.  (This is the Becker--Lubotzky observation
"flexibly stable hyperlinear groups are residually finite", Dogon p. 3,
reproved here to keep the route self-contained; Dogon Prop. 1.11 is the
same conclusion from `(i)` through Kirchberg's factorization property.)

`(iii) => (i)` and `(iii) => (ii)`.  Both Def 1.5 and statement `(ii)` quantify
over hyperlinear approximations of `Gamma`; if `Gamma` is not hyperlinear
there are none (Dogon Def 1.1/1.4 equivalence), so both hold vacuously.
