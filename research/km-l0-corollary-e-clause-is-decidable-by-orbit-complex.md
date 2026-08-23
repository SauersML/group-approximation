---
rg: 2
id: km-l0-corollary-e-clause-is-decidable-by-orbit-complex
kind: claim
title: Decide the L0 clause of Corollary E for the Kac-Moody lattices through the 58-orbit equivariant complex
distinct_from:
  compact-hyperbolic-km-lattices-fail-lp: that is the LP conclusion whose only surviving Ioana--Spaas--Wiersma mechanism is this clause; this is the isolated cohomological decision problem.
  km-group-ring-h2-vanishes-for-the-lattices: that killed the integral group-ring clause; this concerns the measurable-coefficient clause `H^2(Lambda, L^0(Y,R)) != 0` for some ergodic p.m.p. action, which the finite-stabilizer machinery does not decide.
  km-thick-part-two-connected-and-lattice-is-f3: that supplies the 2-connected cocompact model making this clause finitely presented; this asks for the actual computation or a malleability vanishing theorem.
---

**OPEN.**  Decide whether some ergodic p.m.p. action `Lambda
curvearrowright (Y,nu)` of `Lambda = Lambda_(2,4,6)(q)` has
`H^2(Lambda, L^0(Y,R)) != 0` (Ioana--Spaas--Wiersma Corollary E's
surviving clause; a positive answer proves `C^*(Lambda)` fails LP,
completing `compact-hyperbolic-km-lattices-fail-lp`; a proof of
vanishing for all ergodic actions would leave the LP question with NO
known failure mechanism, sharpening the forced-witness fork of
`kac-moody-lattice-is-non-hyperlinear-or-llp-failure`).

Three recorded routes (details on the LP node):

1. **Orbit complex.**  With the thick part 2-connected
   (`km-thick-part-two-connected-and-lattice-is-f3`),
   `H^2(Lambda;L^0(Y)) = H^2` of the explicit 58-orbit equivariant
   cochain complex of `X^/Lambda` with coefficients
   `L^0(Y)^(stabilizer)`: one 4-cell (stabilizer the torus), six
   3-cell, fifteen 2-cell, eighteen 1-cell and nine 0-cell orbits,
   the mixed stabilizers being `T . <U_alpha : alpha in Phi_K^+ cup
   Phi_J^->` for the cotype pair `(J,K)` -- finite by properness,
   with root sets computable from the `(KM2)` generalized Cartan
   matrix.  This makes the clause a concrete (if laborious) relative
   cohomology computation per action.
2. **Sphere pairings.**  The development's explicit 2-spheres impose
   the finite obstruction identities recorded on the LP node; testing
   Bernoulli actions against them is the quickest falsification path.
3. **Malleability.**  A degree-two Popa--Sasyk-type vanishing for
   Bernoulli `L^0`-coefficients over Kazhdan groups would reduce the
   clause to `H^2(Lambda;R) = 0`, already established, killing it.
