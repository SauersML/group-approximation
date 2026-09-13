---
rg: 2
id: atiyah-algebraic-jumps-zariski-closed-proof
kind: route
title: Normal form over D(x_1)[x_2], constant-term evaluation in D((x_1 - beta)), and coordinates of the invariant factors over a Qbar-basis
target: atiyah-algebraic-jumps-lie-in-a-proper-zariski-closed-set
requires: []
artifacts:
  - research/artifacts/atiyah-two-variable-base-change-2026-09-13-part1.md
---

The complete argument is Section 1 of
`research/artifacts/atiyah-two-variable-base-change-2026-09-13-part1.md`.

* **Normal form.** `D(x_1)[x_2]` is a left and right PID, so
  `A = P diag(e_1..e_r, 0..0) Q`.
* **Evaluating `D(x_1)`.** It embeds in `D((x_1 - beta_1))` by the universal
  property of Ore localization. Elements with denominator nonzero at `beta_1`
  lie in `D[[x_1 - beta_1]]`, where taking the constant term is a ring
  homomorphism. A common right denominator `b` of all entries has finitely many
  central roots `B_0`.
* **Where `e_i` vanishes.** Off `B_0`,
  `e_i(beta) = (sum a_ikl beta_1^l beta_2^k) b(beta_1)^-1`. Expanding the
  `a_ikl in D` over a `Qbar`-basis turns `e_i(beta) = 0` into finitely many
  polynomial equations over `Qbar`, not all trivial.
* **Kernel dimension.** Off `Y_A`, `A(beta)` has `D`-rank `r`. By Linnell's
  criterion for Strong Atiyah over `Qbar`, its kernel has dimension `n - r`.
* **Lemma L.** Kernel dimension is upper semicontinuous (Lemma 4 of
  `research/artifacts/atiyah-liouville-base-change-2026-09-12.md`), and
  algebraic points off `Y_A` are dense.
