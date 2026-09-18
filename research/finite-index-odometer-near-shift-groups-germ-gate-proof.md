---
rg: 2
id: finite-index-odometer-near-shift-groups-germ-gate-proof
kind: route
title: Finite index transfers F_infinity and a finitely generated index kernel, and bounded displacement forces linear growth
target: finite-index-odometer-near-shift-groups-pass-the-germ-gate
requires:
  - odometer-prefix-groups-have-fg-index-kernels
  - shell-germ-fp-is-an-ascending-hnn-gate
  - shell-ascending-gate-is-a-finite-window-inclusion
  - shell-germ-group-has-index-two-fiber-product
artifacts: []
---

**Item 1.**
- `B` is `F_infinity` and `ker(chi)` is finitely generated
  (`odometer-prefix-groups-have-fg-index-kernels`). A finite-index subgroup of an
  `F_infinity` group is `F_infinity` (textbook), so `R_nu` is `F_infinity`, in particular
  finitely presented.
- The near index of `R_nu` is the restriction of the near index of `NearSym(N)`, which on
  `B` is `chi`. So `ker(eta) = R_nu ∩ ker(chi)`, a finite-index subgroup of the finitely
  generated group `ker(chi)`, hence finitely generated (Schreier).
- Take `B_0 = ker(eta)` and `eps = 1` in clause (1) of
  `shell-ascending-gate-is-a-finite-window-inclusion`: `B_0` is finitely generated,
  normal, so `B_0 = s B_0 s^-1`, and the union of its shift conjugates is `B_0 = ker(eta)`.
  Clause (1) holds, so the finite window (2) holds by that node.
- Both clauses of `shell-germ-fp-is-an-ascending-hnn-gate` hold, so `Q_nu` is finitely
  presented, and so is `F_nu` (`shell-germ-group-has-index-two-fiber-product`).

**Item 2.**
- Let `C` bound the displacement of every `lambda_g`, `g in S ∪ S^-1`. Then
  `|lambda_w(0)| <= C |w|` for every word `w`.
- The action is free, so `w -> lambda_w(0)` is injective on the ball of radius `R` in
  the Cayley graph of `P`. Its image lies in `[0, C R]`, so the ball has at most `C R + 1`
  elements. `P` has linear growth, so it is virtually cyclic (textbook: a finitely
  generated group of linear growth is virtually `Z`).
- A piece `v y -> w a^c(y)` with `|v| = |w| = k` acts on the corresponding residue class
  as `n = x + h^k r y -> x' + h^k r (y + c)` in the identification `n = r q + i`, so it
  displaces by at most `|x' - x| + h^k r |c|`, a bound independent of `y`. Finitely many
  pieces give a uniform bound.
