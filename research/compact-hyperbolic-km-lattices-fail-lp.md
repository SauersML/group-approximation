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
  `H^2(Lambda, R) != 0` suffices.**  DECIDED 2026-08-23: `H^2(Lambda;
  R) = 0` (`triangle-colimit-rational-h2-vanishes`).  The 2026-08-21
  repair had correctly withdrawn a vanishing argument that assumed a
  contractible cocompact development, but degree two needs only SIMPLE
  CONNECTIVITY of the Levi-triangle development (Bridson--Haefliger
  III.C.3.13): the Cartan--Leray spectral sequence has
  `E_2^(*,1) = 0`, so `H^2(Lambda;Q)` injects into
  `H^2_Lambda(X;Q) = H^2(X/Lambda;Q) = H^2(triangle;Q) = 0`.  The
  trivial-coefficient clause of Corollary E is therefore DEAD at every
  triangle colimit; the earlier tilt toward nonvanishing is withdrawn.
  Only the `L^0(Y,R)` clause survives, in the exact form
  `H^2(Lambda;L^0) = ker( L^0(Y)^T/(sum_i L^0(Y)^(P_i)) -> H^2(X;L^0) )`:
  a `T`-invariant measurable function, not a sum of `P_i`-invariant
  ones, whose equivariant extension to the development is a coboundary
  there.  Simplicity still kills the finite-index detour of ISW Example
  1.3(ii) and Remark 1.2.
- **The `L^0` clause now has an explicit obstruction system
  (2026-08-23).**  By `(RH2)/(RH3)` the class of a `T`-invariant
  `f in L^0(Y,R)` survives to `H^2(Lambda;L^0)` iff the equivariant
  cocycle `c_f` (value `g f` on the 2-cell `g sigma_0`) pairs to zero
  with every 2-cycle of the development.  The explicit sphere family of
  `km-development-has-nonzero-end-cohomology-in-degree-one` therefore
  imposes the concrete identities

      `sum_x eps_x ( g_(x,y_i) - g_(x,y_j) ) f = 0  in L^0(Y,R)`

  over all panel/cone configurations, on top of
  `f notin L^0(Y)^(P_1)+L^0(Y)^(P_2)+L^0(Y)^(P_3)`.  Any candidate
  ergodic action (Bernoulli included) can now be tested against finitely
  many such identities at a time; deciding whether all sphere and
  non-sphere 2-cycle conditions can hold simultaneously with the
  non-degeneracy is the surviving content of Corollary E here.
  Once the twisted-surjectivity chain closes (thick part 2-connected),
  the `L^0` clause becomes FULLY FINITE-PRESENTED: `H^2(Lambda;L^0(Y))
  = H^2_Lambda(X^;L^0)` is the second cohomology of the explicit
  58-orbit equivariant cochain complex of the thick part's quotient
  (orbit cells indexed by cotype pairs `(J,J')`: one 4-cell, six
  3-cells, fifteen 2-cells, eighteen 1-cells, nine 0-cells, with
  finite mixed stabilizers `P_J^+ cap P_(J')^-` -- torus times the
  root subgroups fixing both residues), i.e. group-cohomology-of-an-
  orbifold data with all stabilizers finite and listable from the
  rank-two root combinatorics.  Writing out this complex is the
  concrete route to deciding Corollary E's last clause for Bernoulli
  actions.
  A third route: malleability/deformation techniques (Popa--Sasyk
  computed `H^1` of Bernoulli shifts of relative-(T) groups to be the
  character group, arXiv:math/0310211); a degree-two analogue for
  `L^0(X,R)`-coefficients, if true for Kazhdan groups, would reduce
  Corollary E's clause to `H^2(Lambda;R) = 0` -- already established --
  and kill the LAST known Ioana--Spaas--Wiersma mechanism at these
  lattices, making the LP question fully mechanism-free in the failure
  direction.
- **ISW Corollary D: DEAD (established 2026-08-23).**
  `km-group-ring-h2-vanishes-for-the-lattices` proves
  `H^2(Lambda, Z Lambda) = 0` for the program's lattices in any
  characteristic, so Corollary D can never apply here; the route
  through the development's end cohomology is invalidated.  History of
  the day's analysis follows.  `H^2(Lambda,Z Lambda)` is
  the end cohomology of the development
  (`km-group-ring-h2-is-development-end-cohomology`).  The codistance
  filtration reduces its vanishing to a finite surjectivity
  (`km-twisted-level-product-cycles-surject`); that input failed at
  small `q` only (hexagon levels `q <= 3`, `B_2` at `q = 3`), by
  rational-normal-curve span thresholds verified computationally at
  `q = 2, 3, 4` and vacuous for `q > 1764^3`; an intermediate
  characteristic-two collapse claim was retracted (structure-constant
  bug).  For the actual lattices, in any characteristic, the
  surjectivity is expected (`q >= 8` suffices, pending the
  disjoint-class bookkeeping), whence `H^2(Lambda,Z Lambda) = 0`,
  `Lambda` is type `F_3`, and Corollary D is DEAD alongside the
  trivial-coefficient clause of Corollary E
  (`triangle-colimit-rational-h2-vanishes`).  The `L^0` clause, with
  its sphere-pairing obstruction system, is then the only known
  Ioana--Spaas--Wiersma mechanism for LP failure here.
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
- **Former "surviving concrete route to `H^2(Lambda; R)`" (now
  superseded).**  The non-cocompact quotient `Lambda \\ (X_+ x X_-)`
  computation proposed here is no longer needed for the real
  coefficients: the cocompact development answers it
  (`H^2(Lambda;R)=0`).  The same spectral-sequence bookkeeping applied
  to `X_+ x X_-` expresses `H^2(Lambda;Z Lambda)` as the second
  cohomology of the complex of cochains finitely supported on every
  `Lambda`-orbit of cells; this is an alternative, non-cocompact model
  of the same group identified in
  `km-group-ring-h2-is-development-end-cohomology`.
- **What would NOT follow.**  LP failure says nothing about the LLP
  (the local side, `triangle-relator-extension-admits-local-ucp-
  sections`) — by design of the equivalence; conversely no LLP-side
  progress decides this claim.  The two holes are independent and
  jointly sharper than either alone.
