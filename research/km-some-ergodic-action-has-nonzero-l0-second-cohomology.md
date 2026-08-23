---
rg: 2
id: km-some-ergodic-action-has-nonzero-l0-second-cohomology
kind: claim
title: Some ergodic action of a simple Kazhdan Kac-Moody lattice has nonzero measurable-coefficient second cohomology
distinct_from:
  compact-hyperbolic-km-lattices-fail-lp: that is the LP conclusion whose only surviving Ioana--Spaas--Wiersma mechanism is this clause; this is the isolated cohomological decision problem.
  km-group-ring-h2-vanishes-for-the-lattices: that killed the integral group-ring clause; this concerns the measurable-coefficient clause `H^2(Lambda, L^0(Y,R)) != 0` for some ergodic p.m.p. action, which the finite-stabilizer machinery does not decide.
  km-thick-part-two-connected-and-lattice-is-f3: that supplies the 2-connected cocompact model making this clause finitely presented; this asks for the actual computation or a malleability vanishing theorem.
---

**OPEN.**  Some ergodic p.m.p. action `Lambda curvearrowright (Y,nu)`
of `Lambda = Lambda_(2,4,6)(q)` has `H^2(Lambda, L^0(Y,R)) != 0`
(Ioana--Spaas--Wiersma Corollary E's surviving clause).  Established,
it proves `C^*(Lambda)` fails LP through
`km-lp-fails-via-l0-clause`; its NEGATION (vanishing for every ergodic
action) would leave the LP question with no known failure mechanism,
sharpening the forced-witness fork of
`kac-moody-lattice-is-non-hyperlinear-or-llp-failure`.

Three recorded routes (details on the LP node):

1. **Orbit complex.**  With the thick part 2-connected
   (`km-thick-part-two-connected-and-lattice-is-f3`),
   the reduction is now ESTABLISHED
   (`km-l0-cohomology-is-the-49-orbit-invariants-complex`):
   `H^2(Lambda;L^0(Y))` IS the `H^2` of the finite 49-orbit
   invariants complex of `X^/Lambda` (orbits = pairs of proper
   cotypes `(J,K)`, stabilizers the Birkhoff intersections
   `T . <U_alpha : alpha in Phi_J^- cup Phi_K^+>`), for ANY p.m.p.
   action.  What remains is exactness analysis of that complex per
   action.
2. **Sphere pairings.**  The development's explicit 2-spheres impose
   the finite obstruction identities recorded on the LP node; testing
   Bernoulli actions against them is the quickest falsification path.
3. **Malleability.**  A degree-two Popa--Sasyk-type vanishing for
   Bernoulli `L^0`-coefficients over Kazhdan groups would reduce the
   clause to `H^2(Lambda;R) = 0`, already established, killing it.
