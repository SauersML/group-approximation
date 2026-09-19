---
rg: 2
id: non-rf-kazhdan-weak-ucp-iff-proof
kind: route
title: Kazhdan averaging plus Malcev residual finiteness of finite-dimensional images, and a vacuous converse
target: non-rf-kazhdan-weak-ucp-iff-non-hyperlinear
requires:
  - kazhdan-weak-ucp-stability-is-flexible-stability
---

`(i) <=> (ii)` is `kazhdan-weak-ucp-stability-is-flexible-stability`
(`Gamma` has property (T)).

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

`(iii) => (i)` and `(iii) => (ii)`.  Both Def 1.5 and `(WF1)` quantify
over hyperlinear approximations of `Gamma`; if `Gamma` is not hyperlinear
there are none (Dogon Def 1.1/1.4 equivalence), so both hold vacuously.
