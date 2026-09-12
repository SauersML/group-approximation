---
rg: 2
id: phase-windows-no-separated-clifford-realization-proof
kind: route
title: Ascending relations survive in every finite quotient, so the phase move stays inside one fibre while the sign forces an edge
target: phase-windows-have-no-separated-clifford-realization
requires: []
artifacts:
  - research/artifacts/clifford-cover-phase-barrier-2026-09-12.md
---

Complete direct proof, artifact Section 1.
- **Adjacent.** `c_x c_y` and `c_y c_x` have signs adding to `b_S(x, y)`, whatever the order. A coordinate
  realization keeps both signs, so `b_(S')(lambda x_0, lambda h x_0) = b_S(x_0, h x_0) = 1`.
- **Inseparable.** In a finite quotient `G'/K`, conjugation by `psi(t)` maps the finite image of `B'` into
  itself, so onto itself. Hence `psi(h)` lies in `K B'`, and `B'` fixes `lambda(x_0)`. So
  `lambda(h x_0) = psi(h) lambda(x_0)` lies in `K lambda(x_0)`.
- **Conclusion.** An edge inside a `K`-fibre for every `K` violates both the finite-pullback property and
  saturation condition 1.
- **Kun--Thom instance.** `Gamma = EL_r(F_q[x_1, ..., x_d])` with `r >= 3` is finitely generated. The ascending
  element `t` and the phase element `h = t^(-1) gamma t` are the data of `kun-thom-clifford-radical-phase`.
