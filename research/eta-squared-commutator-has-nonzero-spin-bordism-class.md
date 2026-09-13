---
rg: 2
id: eta-squared-commutator-has-nonzero-spin-bordism-class
kind: claim
title: The eta-squared triple commutator map T^2 x S^3 -> SU(2) has nonzero reduced spin bordism class
distinct_from:
  u2-triple-samelson-class-three-stage: That shows the triple commutator map is not null-homotopic; this shows its mapped spin bordism class is nonzero, the stronger statement a trapping detector can read.
artifacts:
  - research/artifacts/class-three-spin-bordism-trapping-2026-09-12.md
---

Let alpha(s) = diag(s, 1) on S^1 and omega: S^3 = SU(2) -> U(2). Define
c: T^2 x S^3 -> SU(2) by c(s_1, s_2, z) = [alpha(s_2), [alpha(s_1), omega(z)]].
For every spin structure on T^2 x S^3,

    [T^2 x S^3, c]_red != 0  in  Omega-tilde^Spin_5(SU(2)) ≅ Omega^Spin_2 ≅ Z/2.

A regular inverse image of c is a framed surface inside the open top cell.
It represents eta^2 in pi_2^s, and its induced spin structure has Arf
invariant one.

Complete argument. Not independently reviewed. It uses standard
low-dimensional bordism facts without re-verified theorem numbers.
