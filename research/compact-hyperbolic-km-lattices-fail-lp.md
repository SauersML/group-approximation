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
program with `Lambda` as the witness.  The refutation branch of this
claim — "`C*(Lambda_(2,4,6)(q))` has the LP" — is currently the
single shortest conditional statement in the graph that closes the
program.  Every outcome is progress; the missing piece is a single
cohomological input.

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
- **Continuous-cohomology induction: inner fork DECIDED NEGATIVE
  (2026-08-21), by three independent blocks.**  (i) *The degree-2
  vanishing input does not exist.*  The DJ-framework vanishing for a
  BN-pair group acting on its `n`-dimensional building covers degrees
  `1, ..., l` with `l` the compact-link parameter, hence at most
  `n - 1` (Oppenheim arXiv:1512.08188, main BN-pair theorem, read at
  source: `H^i(G, pi) = 0, i = 1, ..., l` for thickness `q >= Q`,
  Hilbert and Banach coefficient classes; and Caprace--Rémy
  Corollary 21 consumes [DJ02, Theorem E] precisely as "the
  1-cohomology vanishing").  For the rank-3 compact-hyperbolic
  factors `n = 2`: the vanishing range stops at degree 1, and degree
  2 is the TOP degree of each factor's building — the
  DDJMO nonvanishing zone; Künneth for `G_+ x G_-` kills only the
  `H^1 (x) H^1` piece (property (T)), leaving the top-degree factor
  pieces untouched.  (ii) *No degree-2 Shapiro bridge exists for
  non-uniform lattices.*  Caprace--Rémy's uniform integrability
  theorem (Theorem 30, verbatim verified: a natural fundamental
  domain, uniformly p-integrable for every `p in [1, infty)`) is
  stated and consumed as a substitute for cocompactness in the
  Gelander--Karlsson--Margulis harmonic-map superrigidity (their
  Corollary 31) — degree-`<= 1` cocycle technology; no published
  statement upgrades any integrability substitute to a degree-2
  Eilenberg--MacLane induction isomorphism.  (iii) *The hoped-for
  principle is false in the classical world.*  ISW Example 1.3(ii)
  ([So78], read at source): the congruence subgroup `Gamma_p <=
  SL_3(Z)` is a non-uniform higher-rank (T) lattice with
  `H^2(Gamma_p, R) != 0` although `H^2_ct(SL_3(R); R) = 0` — ambient
  degree-2 vanishing plus integrability can never imply lattice
  `H^2`-vanishing; classically the lattice classes live in the
  NON-unitary smooth induced module (Borel-type Shapiro with
  `C^infty(G/Gamma)`), outside every unitary vanishing theorem.
  *Tilt:* (i) and (iii) weakly predict `H^2(Lambda; R) != 0`
  (Corollary E LIVE) — degree 2 is exactly where the buildings carry
  cohomology and where non-uniform (T) lattices are known to hide
  classes — but the known class-producing mechanism (congruence
  level structure) has no analogue in a simple group.  The outer
  fork stays genuinely open, with the inner fork closed.
- **Surviving concrete route to `H^2(Lambda; R)`.**  After
  barycentric subdivision, `Lambda` acts cellularly, properly, with
  finite stabilizers on the contractible locally finite 4-complex
  `X_+ x X_-`, so the equivariant spectral sequence with rational
  coefficients collapses (finite stabilizers are Q-acyclic) to

      `H^k(Lambda; Q) = H^k(Lambda \ (X_+ x X_-); Q)`  for all k,

  with NO cocompactness needed.  The quotient is an explicit
  infinite 4-complex: chamber-pair cells are indexed by the
  codistance in `W` (twin strong transitivity), lower cells by
  parabolic double-coset data.  Computing its `H^2` is the honest
  open computation that replaces every vanished shortcut — and is
  the corrected form of the repaired wrong claim: the erroneous step
  had quotiented a cocompact model that does not exist; the
  non-cocompact quotient computation is what actually remains.
- **What would NOT follow.**  LP failure says nothing about the LLP
  (the local side, `triangle-relator-extension-admits-local-ucp-
  sections`) — by design of the equivalence; conversely no LLP-side
  progress decides this claim.  The two holes are independent and
  jointly sharper than either alone.
