---
rg: 2
id: bkm-test-transparency-proof
kind: route
title: Specialize the derived-unique-game bound to kappa=1 and invert it for a reduction
target: bkm-test-transparent-on-learnable-games
requires: []
artifacts:
  - research/artifacts/unique-games-bkm-test-transparency-2026-09-11.md
---

The artifact proves the per-instance inequality
`val(R_(rho,m)(Psi)) >= 1/m+(1-1/m)rho^3 val(UG_der(Psi))^2 - 2e(Psi)`
in full (Theorem 1), so this route is complete against it; the same inequality
is recorded as the standalone lemma `derived-unique-game-lower-bounds-the-noise-test`
(ugc-1's node, credited to ugc-2), and this route may be refactored to require
that id once it is on main. All three parts read off the inequality.

1. Distinct matchings give `|F_e|` classes each of one edge, so a right
   labeling can be matched by choosing, per class, the fiber over the
   satisfied edge's right label; `val(UG_der)=1`. Substitute.

2. Completeness of `UG_der` is `val(UG_der(Psi)) >= val(Psi) >= 1-eta`.
   Soundness: the hypotheses give
   `(1-1/m)rho^3 val(UG_der(Psi))^2 <= val(R(Psi)) - 1/m + 2e(Psi) <= epsilon + 2xi`,
   hence `val(UG_der(Psi)) <= sqrt((epsilon+2xi)/((1-1/m)rho^3)) = s`. So
   `UG_der` separates `1-eta` from `s`, and the map is polynomial-time by the
   construction in `derived-unique-game-lower-bounds-the-noise-test`.

3. Contrapositive of the soundness clause: if `val(UG_der(Psi))` stayed bounded
   below by a constant on a family with `e(Psi)=o(1)`, then `val(R(Psi))` would
   be bounded below by a constant, contradicting `val(R(Psi))<=epsilon`.

Full statement and the finite gap example are in the artifact.
