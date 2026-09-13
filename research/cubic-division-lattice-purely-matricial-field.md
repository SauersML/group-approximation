---
rg: 2
id: cubic-division-lattice-purely-matricial-field
kind: claim
title: Some cocompact lattice SL_1(O_D) from a cubic division algebra is purely matricial field
distinct_from:
  sl3z-purely-matricial-field: that is the non-cocompact lattice SL_3(Z) with unipotents, block and principal SL_2 subgroups; this is a cocompact Kazhdan lattice with no nonamenable proper algebraic subgroups at all.
---

OPEN.  For some central division algebra `D` of degree 3 over `Q`, the
cocompact Kazhdan lattice `Gamma_D = SL_1(O_D) < SL_3(R)` has finite-dimensional
unitary representations converging strongly to its regular representation.

Why this is the sharpest Kazhdan target for genuine representations.  It is an
infinite property (T) group, residually finite through the congruence quotients
`SL_3(F_p)` at split primes, and by
`cubic-division-lattice-subgroups-are-zariski-dense` every nonamenable subgroup
is Zariski dense: no invariant-vector witness of the Magee--de la Salle kind
exists at large levels, and there are no unipotent elements, no relative
property (T) pairs `(Z^2 x| SL_2(Z), Z^2)`, and no block or principal `SL_2`.
A positive answer settles `infinite-kazhdan-group-with-mf-reduced-cstar`.

## Attempts

* **Invariant-vector obstruction.**  Absent at large levels
  (`cubic-division-lattice-subgroups-are-zariski-dense`).  No other obstruction
  to strong convergence for `Gamma_D` is recorded.
* **Automorphic temperedness of congruence quotients.**  Not a proof.
  Temperedness of the automorphic spectrum of `L^2(Gamma(N) \ SL_3(R))`
  controls Hecke operators, i.e. radial elements of the group algebra relative
  to a maximal compact subgroup.  Strong convergence needs every element of
  `C[Gamma_D]`, a noncommutative non-Hecke algebra.  Van Handel's survey
  (arXiv:2510.12520, Section 2.2) records deterministic number-theoretic strong
  convergence as open even for free groups and Lubotzky--Phillips--Sarnak
  graphs.  The Ramanujan conjecture for `GL_3` over `Q` is itself open; the
  function-field analogues (Cartwright--Steger lattices acting on `A~_2`
  buildings, Lafforgue) would supply temperedness but not the non-Hecke
  elements.
* **Which constituents.**  As for `SL_3(Z)`, the regular representations of
  `SL_3(F_p)` contain the trivial representation, so a selection of irreducible
  constituents is needed.  Theorem B of the artifact shows no nonamenable
  subgroup forces a fixed vector in the nontrivial ones at large `p`; whether
  the nontrivial part of `l^2(SL_3(F_p))` restricted to `Gamma_D` converges
  strongly is the concrete open question.
