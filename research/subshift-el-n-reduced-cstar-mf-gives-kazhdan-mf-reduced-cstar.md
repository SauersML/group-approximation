---
rg: 2
id: subshift-el-n-reduced-cstar-mf-gives-kazhdan-mf-reduced-cstar
kind: route
title: An MF reduced C*-algebra of EL_n over a minimal subshift ring would give an infinite Kazhdan group with MF reduced C*-algebra
target: infinite-kazhdan-group-with-mf-reduced-cstar
requires:
  - directly-finite-subshift-el-n-reduced-cstar-is-mf
  - minimal-subshift-algebra-is-simple-lef-ring
  - elementary-groups-over-fg-rings-have-property-t
---

Let `X` be an infinite minimal subshift over a finite alphabet, `q` a prime power, `R_X = LC(X,F_q) ⋊ Z`, and `n ≥ 4`.

1. `R_X` is finitely generated and LEF as a ring (`minimal-subshift-algebra-is-simple-lef-ring`). A LEF ring embeds
   unitally in an algebraic ultraproduct of matrix rings, where `ab = 1` forces `ba = 1`. So `R_X` is directly finite,
   which is the hypothesis of `directly-finite-subshift-el-n-reduced-cstar-is-mf`.
2. `EL_n(R_X)` has property (T) (`elementary-groups-over-fg-rings-have-property-t`), and it is infinite because
   `e_12(LC(X,F_q))` is infinite.
3. If `directly-finite-subshift-el-n-reduced-cstar-is-mf` holds, `C*_r(EL_n(R_X))` is MF, so `EL_n(R_X)` is an infinite
   Kazhdan group with MF reduced C*-algebra. ∎

Only the first requirement is open, so this route is live but incomplete. It records that the note's groups are
candidates for `infinite-kazhdan-group-with-mf-reduced-cstar` (sk-cairn-steward, 2026-09-13).
