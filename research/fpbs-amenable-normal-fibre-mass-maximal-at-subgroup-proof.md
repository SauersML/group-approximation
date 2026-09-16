---
rg: 2
id: fpbs-amenable-normal-fibre-mass-maximal-at-subgroup-proof
kind: route
title: Cauchy–Schwarz for the connection kernel on a Følner set and its right translate
target: fpbs-amenable-normal-fibre-mass-maximal-at-subgroup
requires: []
artifacts:
  - research/artifacts/fpbs-amenable-normal-fibre-mass-bound-2026-09-16.md
---

Theorem A and Corollaries B–E of the artifact.

* **Kernel.** `tau_p(x,y) = phi_p(x^(-1) y)` is positive semidefinite, because
  `sum_(x,y) conj(a_x) a_y 1{x <-> y} = sum_C |sum_(x in C) a_x|^2` over
  clusters `C`. So `<u,tau v> <= <u,tau u>^(1/2) <v,tau v>^(1/2)` for
  finitely supported real `u`, `v`.
* **Pair counts.** Take finite `F_n ⊆ H` with `|F_n m \ F_n|/|F_n| -> 0` for all
  `m in H`, and put `c_n(m) = |F_n ∩ F_n m^(-1)|`. Then `c_n <= |F_n|` and
  `c_n(m)/|F_n| -> 1`.
* **Three sums.** With `u = 1_(F_n)` and `v = 1_(F_n g)`, grouping pairs by
  `m = h^(-1) k`:
  * `<u,tau v> = sum_(m in H) c_n(m) phi_p(mg)`;
  * `<u,tau u> <= |F_n| chi^H_p`;
  * `<v,tau v> = sum_(m in H) c_n(m) phi_p(g^(-1) m g) <= |F_n| chi^(g^(-1)Hg)_p`.
* **Limit.** Fatou's lemma bounds `chi^(Hg)_p` by
  `liminf <u,tau v>/|F_n|`. Cauchy–Schwarz bounds that by the geometric mean.
  Invariance and symmetry give `chi^(Hg)_p = E_p|K_g ∩ H|`.
* **Normal case.** `g^(-1) H g = H` and `Hg = Gamma_q`. Inversion gives the
  symmetry in `q`.
* **Positive definiteness.** Lift `a : Q -> C` to
  `A_n = sum_q a_q 1_(F_n s(q))` for a section `s`. Then
  `<A_n, tau A_n>/|F_n| >= 0` converges to
  `sum_(q,q') conj(a_q) a_(q') sigma_p(q^(-1) q')`, by dominated convergence
  with the bound `sigma_p <= chi^H_p < infinity`.
* **Commensurability.** Write `H = ⊔_i L_0 c_i` with `c_i in H`, and apply the
  theorem to `L_0` and `g = c_i`, using `c_i^(-1) L_0 c_i = L_0`.
* **Sphere bubbles.** `sigma_p^2 <= (sup sigma_p) sigma_p`.
