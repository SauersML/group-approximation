# Major-problems swarm: priority check and 2025–26 tools (lit-major, 2026-09-12)

Scout lane `lit-major`, early afternoon CDT. It checked the swarm lanes' named problems for recent public
solutions and forwarded verified tools to lanes, one message per lane.

Method and limits:
- The morning check `research/artifacts/lane-priority-literature-check-2026-09-12.md` scanned the arXiv
  recent lists and August 2026 lists. It is not repeated here, because no new arXiv announcement falls
  between that check and this one.
- About 15 targeted web searches, 2024 to September 2026, one or more per lane. The session's web-search
  budget ran out after them, so later leads could not be searched.
- Items marked **[PDF]** were read from text extracted on MSI with ghostscript. Items
  marked **[abstract]** were read from the arXiv abstract page only.
- The arXiv API returned HTTP 429, so title searches were unavailable.
- Nothing here is imported into Cairn. Lanes add -citation routes when they use a statement.

## Priority threats: none found

No public source found settles any of these:
- a non-hyperlinear group; Pestov Q3.4;
- nonsofic or non-RF hyperbolic groups;
- Gottschalk; Kaplansky direct finiteness; Kervaire–Laudenbach;
- Strong Atiyah for torsion-free groups; Lück's determinant conjecture;
- p_c < p_u in general; Gaboriau's fixed price problem;
- Toms–Winter; the quasitrace problem; the UCT problem;
- Baum–Connes; Kadison–Kaplansky; the zero-divisor conjecture;
- amenability of Thompson's F.

**False alarm.** A web search summary asserted "every discrete group satisfies Lück's determinant
conjecture". The source is Manzoor, arXiv:2508.15154v2 **[abstract]** (already cited in Cairn), which proves
only an IRS statement: "For every free group, we prove the existence of an IRS satisfying the determinant
conjecture that is not co-hyperlinear, and hence not co-sofic. This provides evidence that satisfying the
determinant conjecture might be a weaker property than soficity for groups, and consequently the conjecture
possibly holds for all groups." The conjecture for groups remains open.

## Tools forwarded to lanes (not yet in Cairn unless noted)

### `gottschalk-rokhlin-lower-bound`

Seward, *The Koopman representation and positive Rokhlin entropy*, arXiv:1804.05270v1 **[PDF]**. It
applies to every countably infinite group; no soficity is assumed.

> Theorem 1.2. Let G y (X,µ) be a free p.m.p. action, and let ρ : G → U(L²(X,µ)) be the corresponding
> Koopman representation. Also let λ : G → U(ℓ²(G)) be the left-regular representation. If H is a
> ρ(G)-invariant closed subspace of L²(X,µ) and ρ|_H is singular with λ, then h_G(σ-alg(H)) = 0.

> [Theorem 1.1] implies that λ^{⊕N} embeds into the Koopman representation of any free ergodic p.m.p.
> action with positive Rokhlin entropy.

Corollary 1.3: a Gaussian action induced by an orthogonal representation singular with λ_R has zero
Rokhlin entropy. Corollary 1.5: CPE⁺ actions have Koopman representation isomorphic to λ^{⊕N}.

These are necessary conditions on any positive-entropy action. They give no lower bound.

### `hyperbolic-rf-alternating`

Caprace–Conder–Kaluba–Witzel, *Hyperbolic generalized triangle groups, property (T) and finite simple
quotients*, arXiv:2011.09276v2 **[abstract]**. Text extraction on MSI gave only table pages, so it was
not read from the PDF.

> some of those hyperbolic Kazhdan groups possess finite simple quotient groups of arbitrarily large rank;
> they constitute the first known specimens combining those properties.

The lane was also pointed to the PDF-verified Lubotzky 2005 Remark 4.2 and Sisto–Wilton arXiv:2410.00556
in `research/artifacts/lit-scout-2-findings-2026-09-12.md`.

### `toms-winter-w-bundles`

Two sources, both **[abstract]**:
- Kerr–Kopsacheilis–Petrakos, arXiv:2404.04634v2: "for every minimal action of a countably infinite
  discrete group on a compact metrizable space, if the extreme boundary of the simplex of invariant Borel
  probability measures is closed and has finite covering dimension then the action has the small boundary
  property."
- Kopsacheilis–Liao–Tikuisis–Vaccaro, arXiv:2406.09808v4: for free actions of countably infinite amenable
  groups, uniform property Γ of the Cartan subalgebra C(X) ⊆ C(X) ⋊ G is equivalent (with Kerr–Szabó) to
  the small boundary property. For minimal actions, tracial Z-stability of the subalgebra gives almost
  finiteness.

### `thompson-f-amenability`

Guba, *Amenability problem for Thompson's group F: state of the art*, arXiv:2305.07113v4 **[abstract]**:
"a survey of our recent results on the amenability problem for Thompson's group F. They mostly concern
estimating the density of finite subgraphs in Cayley graphs of F for various systems of generators, and also
equations in the group ring of F. We also discuss possible approaches to solve the problem in both
directions." Caution: older arXiv non-amenability claims (e.g. arXiv:1408.2188) are not accepted results.

### `determinant-positivity`

The false-alarm clarification above.

## Checked, already in Cairn, not re-forwarded

- Choi–Seo arXiv:2508.08932, p_c < p_u for acylindrically hyperbolic groups.
- Dogon arXiv:2211.10492 and Dogon–Vigdorovich arXiv:2506.20843, HS stability versus hyperlinearity.
- Local HS stability, arXiv:2307.13155.
- Garg–Mineyev arXiv:2501.07646v2 (Sep 2025): no taiko counterexamples for 1 ≤ m, n ≤ 13.
- Meyer arXiv:2508.05726: Chabert–Echterhoff extension permanence for Baum–Connes cannot be weakened to N
  alone.
- Mikheenko arXiv:2505.12783, unimodular equations and derived length.
- Sánchez-Peralta arXiv:2409.12268: Atiyah permanence over finite edge groups only.
- Paddock–Slofstra arXiv:2310.07901; arXiv:2505.05253.
- Abert–Nikolov math/0701361.

## Seen, not forwarded

- Zhongyang Li, arXiv:2601.09958v2 **[abstract]**: planar site percolation, p_u^site ≥ 1 − p_c^site under
  countably many end classes. Planar only, so it does not bear on the F₂×Z lanes.
- Dogon–Levit–Vigdorovich, arXiv:2407.11608v2 **[abstract]**: quantitative HS stability of amenable groups
  (stability radius growth). Not relevant to Kazhdan cruxes.
- Phung, arXiv:2503.23435: surjunctivity of non-uniform CA over surjunctive groups. Tangential.

## Unverified lead (not forwarded)

"RE-completeness of entangled constraint satisfaction problems" (a ResearchGate listing, February 2026)
reportedly shows that entangled versions of all boolean CSPs (3SAT, 2-CSPs such as k-colouring) are
RE-complete. That could bear on the affine pp-definability barrier of `nh-affine-barrier`. The arXiv id and
statement were not identified before the search budget ran out. Verify before use.
