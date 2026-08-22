---
rg: 2
id: compact-hyperbolic-km-lattices-fail-lp
kind: claim
title: The full C*-algebras of the simple Kazhdan Kac-Moody lattices do not have the lifting property
artifacts:
  - research/artifacts/isw-ddjmo-cr-cohomology-sources-2026-08-21.md
distinct_from:
  non-rf-kazhdan-group-with-llp-full-c-star-algebra: that asks for a group whose full algebra HAS the local lifting property; this predicts the failure of the stronger global LP at the Kac--Moody candidates, and its negation (LP holding) would close that hole outright rather than compete with it.
  triangle-colimit-llp-reduces-to-relator-local-splitting: that equivalence decides nothing about either side; this is the open global side: by that node, this claim says exactly that no triangle presentation's relator extension is globally ucp-split.
  triangle-relator-extension-admits-local-ucp-sections: that is the open LOCAL splitting (= LLP); this is the expected failure of GLOBAL splitting (= LP); together they would pin the Kac--Moody LLP question as a strict local-vs-global separation, which no current example exhibits.
  km-lattices-admit-no-cocompact-npc-model: that is an established geometric no-go used here to explain why the cohomological input is hard to compute; this is the C*-conclusion that the input would feed.
---

OPEN CLAIM.  Let `Lambda` be a compact-hyperbolic-type simple Kazhdan
Kac--Moody lattice as in `simple-kazhdan-kac-moody-lattices-exist`
(e.g. `Lambda_(2,4,6)(q)`, `q > 1764^3`).  Then `C*(Lambda)` does NOT
have the lifting property (LP).

**Stakes both ways (a win-win fork).**  If this holds, then by
`triangle-colimit-llp-reduces-to-relator-local-splitting` no triangle
presentation's relator extension is globally ucp-split, so the LLP
hole at `Lambda` becomes a pure local-vs-global splitting question —
and `Lambda` would be the first LP failure at a group with no
finite-dimensional representations at all (the
Ioana--Spaas--Wiersma cohomological mechanism, unlike their Theorem A
projective-representation mechanism, is NOT a priori vacuous at
simple groups).  If instead it FAILS — `C*(Lambda)` has the LP —
then a fortiori `C*(Lambda)` has the LLP, and
`llp-non-rf-kazhdan-group-is-non-hyperlinear` closes the whole
program with `Lambda` as the witness.  Every outcome is progress;
the missing piece is a single cohomological input.

## Attempts

- **ISW Corollary D (source-verified verbatim this date): needs
  `H^2(Lambda, Z Lambda) != 0`.**  No recorded model computes
  `H^*(Lambda, Z Lambda)`.  Brown's criterion
  (`H^k(Gamma, Z Gamma) = H^k_c(model)`) needs a proper cocompact
  contractible model, and `km-lattices-admit-no-cocompact-npc-model`
  shows the CAT(0) route to one is closed: the twin product
  `X_+ x X_-` is proper but non-cocompact (Caprace--Rémy at source),
  a single building is cocompact-like but non-proper (infinite
  chamber stabilizers), and the triangle development is proper
  cocompact but never CAT(0), with contractibility unknown.  The
  exactly-missing fact is `H^2(Lambda, Z Lambda) != 0`, or any
  finiteness model strong enough to compute it.
- **The building-side cohomology is available and nonzero; only the
  bridge is missing.**  Davis--Dymara--Januszkiewicz--Meier--Okun
  arXiv:0806.2412 (read at source) compute `H^*_c` of every
  finite-thickness building realization (Main Theorem/Cor 8.2) with
  top-degree concentration for the classical realization (Thm 4.3).
  Nonvanishing in our dimension is elementary: the retraction
  `rho_{A,c}` of the building onto an apartment `A` is proper (finite
  thickness makes gallery-balls finite), the inclusion `A -> X` is
  proper, and `rho o incl = id`, so `H^2_c(A) = H^2_c(R^2) = Z`
  embeds into `H^2_c(X)`.  But `Lambda` is not proper on `X_+`, and
  the DDJMO lattice corollary (their Cor 9.4) needs torsion-free
  cocompact lattices in `Aut(X)` — `Lambda` is neither (root-group
  torsion; non-discrete image).  The cohomology exists; no recorded
  theorem transports it to `H^2(Lambda, Z Lambda)`.
- **ISW Corollary E (source-verified verbatim): needs an ergodic
  p.m.p. action with `H^2(Lambda, L^0(X, R)) != 0`; in particular
  `H^2(Lambda, R) != 0` suffices.**  `H^2(Lambda; R)` is UNRECORDED
  (an earlier assertion of vanishing in this lane was WRONG — it
  assumed a contractible cocompact development, repaired 2026-08-21;
  the NPC route to contractibility is now provably closed).
  Simplicity kills the finite-index detour of ISW Example 1.3(ii)
  and Remark 1.2 (no congruence subgroups to retreat to).  Candidate
  actions: Bernoulli — note ISW's own proof of Corollary D runs
  through Bernoulli-coefficient cocycles `L^0(T^Gamma, T)` and Popa
  malleability, so the `Z Gamma` and p.m.p. routes converge on the
  same kind of soft-coefficient 2-cocycle nonvanishing.
- **Continuous-cohomology route (the other side of the fork).**  The
  (T) input for `Lambda` is Dymara--Januszkiewicz cohomology
  vanishing ([DJ02, Theorem E], per Caprace--Rémy Corollary 21 read
  at source — the origin of the 1764 bound).  If a DJ-type vanishing
  in degree 2 applied to modules induced from the NON-uniform lattice
  (Caprace--Rémy's uniform-integrability theorem is their recorded
  substitute for cocompactness in rigidity, and whether it supports
  Eckmann--Shapiro induction in degree 2 is unrecorded), it would
  prove `H^2(Lambda, R) = 0` and mute Corollary E's easy clause,
  pushing everything to the `Z Lambda` / `L^0`-coefficient routes.
  Neither direction of this inner fork is decided; deciding it is the
  cheapest decisive sub-task on this claim.
- **What would NOT follow.**  LP failure says nothing about the LLP
  (the local side, `triangle-relator-extension-admits-local-ucp-
  sections`) — by design of the equivalence; conversely no LLP-side
  progress decides this claim.  The two holes are independent and
  jointly sharper than either alone.
