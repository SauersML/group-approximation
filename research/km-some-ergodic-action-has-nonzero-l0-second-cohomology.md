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

## Attempts

- 2026-08-23 (post-reduction observations).  The established reduction
  applies to EVERY uniquely divisible module, hence simultaneously to
  `L^0(Y)`, `L^2_0(Y)` and `l^2(Lambda)`; the invariants are
  `l^2(F\Lambda)` resp. `L^0(Y/F)`.  For the BERNOULLI action the
  chaos decomposition writes `L^2_0(Y)` as a sum over `Lambda`-orbits
  of nonempty finite subsets `A` of `Lambda` of modules induced from
  the setwise stabilizers `{g : gA = A}`, which are FINITE (freeness
  of left translation embeds them into `A`).  So the `L^2`-avatar of
  the clause is governed by `H^2(Lambda; l^2(Lambda))`-type invariants
  -- the second l^2-Betti number of `Lambda`, computable from the SAME
  49-orbit complex with `l^2(F\Lambda)` entries.  Honest subquestion,
  not settled today: is `beta_2^(2)(Lambda) = 0`?  (Heuristic:
  Dymara--Januszkiewicz concentration of building L^2-cohomology in
  top degree suggests the product concentrates in degree four, but
  `Lambda` is cocompact only on the thick part, not on `Z`, so this
  needs the cusp analysis rerun for reduced L^2 -- NOT automatic.)
  Caution for the transfer: degree-one cocycle superrigidity
  (Popa--Sasyk) shows `L^2`-nonvanishing can die in `L^0`, so an
  `l^2` computation in either direction only bounds, never decides,
  the `L^0` clause; it selects which of the three recorded routes is
  live.

- 2026-08-23 (double-complex scheme).  Via
  `km-l0-cohomology-is-the-49-orbit-invariants-complex` the complex is
  the total complex of a 3x3 double complex over `Delta^2 x Delta^2`;
  the fixed-`K` columns compute `H^*_(P_K^-)(O(sigma_K); V)` with
  `O(sigma_K)` the (face-)opposition complexes in `X_+`, spherical by
  Abramenko.  Since the unipotent radicals are locally finite
  (increasing unions of the finite `U_w`), `H^2(B_-, V) = 0` for every
  divisible `V` by the Milnor `lim^1` sequence, and the clause reduces
  to two computable kinds of terms: `lim^1` of unipotent invariant
  towers (degree-1 column terms) and `B_-`-equivariant functionals on
  `H_2` of opposition complexes (degree-2 column terms), coupled by
  the second-page differentials.  Derivation: artifact Addendum 9.
  This is the sharpest available formulation of route 1.

- 2026-08-23 (lim^1 mechanism; sharpest state).  The (K-degree 1,
  J-degree 1) entry of the double complex DEGENERATES (both adjacent
  differentials leave the triangle range), so exactly:
  `H^2(Lambda, L^0(Y))` contains as a filtration subquotient the `H^1`
  over the `K`-triangle of `K |-> H^1(P_K^-, L^0(Y))`, and these are
  derived limits (`lim^1`) of unipotent averaging towers by local
  finiteness.  For BERNOULLI the bottom row vanishes (restriction to
  any infinite subgroup is mixing, so parabolic invariants are
  constants), and the model `lim^1` of the TAIL tower of an i.i.d.
  sequence is PROVED nonzero by a characteristic-function argument
  (artifact Addendum 10).  Remaining sharp subquestion:
  `H^1(B_-, L^0(Y)) != 0`?  (invariance is weaker than
  tail-measurability, so the model theorem does not yet transfer),
  then survival across the `K`-direction `H^1`.  If both hold, LP
  FAILS for `C*(Lambda)` and the fork resolves to the LLP-failure
  branch.

- 2026-08-23 (stable-element endgame; state of the art).  PROVED
  today (`locally-finite-bernoulli-first-l0-cohomology-nonzero`):
  every negative parabolic has `H^1(P_K^-, L^0(Y)) != 0` on the
  Bernoulli action.  Finite index of `B_-` in every `P_K^-` makes
  all K-direction restrictions injective with Cartan--Eilenberg
  stable-element images `St_K`, so `E_2^(1,1)` is the linear algebra
  of the subspaces `St_K` of `H^1(B_-, L^0)`; `(St_2 cap St_3)/
  St_23` maps into it and is measured by an explicit well-defined
  obstruction `obs : St_2 cap St_3 -> Hom(N, L^0)^(P_23^-)` on the
  free Bass--Serre kernel `N` of `P_2^- *_(B_-) P_3^- ->> P_23^-`
  (trivial N-action collapses the five-term sequence).  Candidate
  nonvanishing certificates: level data `e_k = sum_b lambda_b F_b`
  with `lambda` mean-zero on both mid-parabolic orbit partitions of
  `M_k \ M_(k+1)` -- an annihilator-existence question of the same
  walk-graph type as `km-opposition-class-walk-threshold-law`.
  Full derivation and the three open caveats: artifact Addendum 11.
  If `obs != 0`: `H^2(Lambda, L^0) != 0` and C*(Lambda) has NO LP
  (Corollary E); the LLP consequence additionally needs an
  unverified `LLP => LP` bridge for (T) groups.

- 2026-08-23 (final collapse of the day).  Two lemmas (artifact
  Addendum 12): (1) the relator obstruction `obs` VANISHES on every
  jointly-invariant tower datum (common telescoping formula
  `c~(w) = (1-w) S_n`), so joint data always extends to the vertex;
  (2) tower six-term + Milnor identifies
  `(St_2 cap St_3)/St_23 ~= coker(H^1(P_23^-, L^0) ->
  H^1(P_2^-, L^0) (+) H^1(P_3^-, L^0))`.  The clause's sharpest
  remaining sub-question is therefore the SURJECTIVITY of one
  vertex-to-edges restriction map on first L^0-cohomology of locally
  finite parabolics; non-surjectivity feeds `E_2^(1,1)` and kills
  LP, surjectivity at all three vertices (plus the (0,2) opposition
  entries vanishing) kills the last known Corollary E mechanism for
  Bernoulli actions.
