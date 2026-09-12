---
rg: 2
id: blackadar-kirchberg-for-uct-quotient-extensions
kind: claim
title: A stably finite extension of a nuclear UCT quasidiagonal algebra by a nuclear quasidiagonal ideal is quasidiagonal
root: true
distinct_from:
  stw99-problem-vii-blackadar-kirchberg: that is the full nuclear stably finite question; this is its special case for extensions of quasidiagonal pieces with UCT quotient (Moutzouris' Conjecture 1.2 with UCT quotient).
  moutzouris-qd-extensions-y-class: that is the established case for ideals locally approximated by the class Y after tensoring with Q; this allows every separable nuclear quasidiagonal ideal.
  stw07-surjective-pullbacks-preserve-nuclear-qd-finiteness: that glues quasidiagonal pieces by surjective pullbacks, which never produce a nonzero index map; this concerns genuine extensions with arbitrary index maps.
artifacts:
  - research/artifacts/stw07-k0-hahn-banach-trace-sign-2026-09-11.md
---

**OPEN.**  Let `0 -> I -> E -> B -> 0` be exact with `I` separable, nuclear and
quasidiagonal, and `B` separable, nuclear, quasidiagonal and UCT.  Then `E` is
quasidiagonal if and only if it is stably finite (equivalently, by Spielberg,
`d(K_1(B)) cap K_0^+(I) = {0}`).

This is the extension case of STW Problem VII (Moutzouris, Conjecture 1.2,
with the UCT imposed on the quotient).

## Attempts

- **Via the K_0-Hahn--Banach property.**  Route
  `bk-uct-extensions-via-k0-hahn-banach`: Brown--Dadarlat Theorem 4.11 plus
  Moutzouris Remark 2.5.  The open prerequisite has been decomposed into the
  exact X(1) residual and a boundary-class hole.
- **Established subclass.**  `moutzouris-qd-extensions-y-class` (ideals
  locally ASH or minimal crossed products after tensoring with `Q`,
  including simple unital UCT ideals).
- **A counterexample here refutes Problem VII too.**  The circle extension of
  `stw07-qd-trace-positive-class-kills-qd-extension` has UCT quotient `C(T)`.
