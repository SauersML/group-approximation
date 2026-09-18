---
rg: 2
id: kazhdan-subgroups-of-brin-thompson-groups-are-finite
kind: claim
title: For every n, every subgroup of the Brin-Thompson group nV with property (T) is finite
distinct_from:
  thompson-v-has-haagerup-property: that is Farley's theorem for V = 1V, which gives this finiteness for n = 1 through a proper action; this asks for the finiteness for every n, where no proper action and no commensurated subset are known.
  kazhdan-subgroups-of-rover-nekrashevych-groups-are-rf: that treats Rover-Nekrashevych groups over one tree, where a commensurated set of cones exists; this treats the product Cantor cubes of nV, where subcubes are not commensurated.
  some-hyperbolic-group-embeds-in-no-brin-thompson-group: that is the negative answer to Zaremsky 2.19(a), which this claim implies but which could also come from another obstruction; this is the finiteness of all Kazhdan subgroups of all nV.
---

For every `n ≥ 1` and every subgroup `K ≤ nV` with property (T), `K` is finite.

## Status

- **n = 1.** Established (`thompson-v-has-haagerup-property`). Also, FW subgroups
  of V are finite (`fw-subgroups-of-eventually-similar-groups-virtually-embed`,
  case of canonical similarities).
- **n ≥ 2.** Open.

## What it would give

- Zaremsky Problem 2.19(a) has answer no. No infinite hyperbolic Kazhdan group
  embeds in any nV (route `some-hyperbolic-group-in-no-nv-via-kazhdan-finiteness`).
- Zaremsky 2.19(c) and 2.19(d) have answer no, because SL_3(Z) has property (T).
- No nV has property (T), which settles the (T) half of Zaremsky Problem 2.7
  (`zaremsky-2-07-brin-thompson-nv-haagerup-or-t`) negatively. It does not
  settle the Haagerup half.
- The claim follows from the Haagerup property of nV for infinitely many n,
  since jV embeds in kV for j < k. It is weaker than that property.

## Attempts

- 2026-09-13 (lane z2-19-hyperbolic-nv, unreviewed): **commensurated subcubes
  fail for n ≥ 2.**
  - The V proof commensurates the set of cones. For nV the set of subcubes is not
    commensurated.
  - Let `C = {0,1}^ω`. The rearrangement of `C^2` fixing `C×[0]` and swapping
    `[0]×[1]` with `[1]×[1]` by changing the first digit of coordinate 1 sends
    `[w]×C` to `[w]×[0] ∪ [w']×[1]` with `w' ≠ w`, which is not a subcube, for
    every nonempty prefix `w`.
  - Restricting to diagonal or fat subcubes removes the broken ones but not the
    problem. An element with prefix-length change vector `s` on a piece changes
    the shape by `s`, so every family defined by a shape condition has infinite
    symmetric difference with its image once `s` is not constant.
- 2026-09-13, same lane, unreviewed: **orbit isoperimetry gives nothing.**
  - Orbits of nV on `C^n` carry the prefix-replacement metric, and elements act
    with bounded displacement.
  - Such orbits are coarsely products of trees, so they are non-amenable, and a
    Kazhdan group acting with non-amenable Schreier graphs is not excluded.
  - Contrast: inside 2V the baker's map `(0x, y) ↦ (x, 0y)`, `(1x, y) ↦ (x, 1y)`
    is conjugate to the two-sided full shift, so the topological full group of
    the full shift embeds in 2V.
  - Its orbits are copies of Z, so a finitely generated Kazhdan subgroup `K`
    acts on each orbit with displacement bounded by a constant `r`. Infinite
    orbits are amenable Schreier graphs, so all orbits are finite.
  - On a finite orbit of size `N`, the Schreier graph has bandwidth at most `r`,
    so it has a balanced cut with at most `O(r^2)` edges. The Kazhdan spectral
    gap then bounds `N`.
  - Uniformly bounded orbits give finitely many finite quotients, so `K` is
    finite.
  - So that subgroup of 2V contains no infinite Kazhdan group. The argument uses
    amenable orbits and does not extend to nV.
- 2026-09-13, same lane: **proper cubical actions are excluded for n ≥ 2.**
  - Callard–Salo (arXiv:2208.00685, Corollary 1.2) and Kojima–Sheng
    (arXiv:2603.18410, Corollary 4.3) state that mV has no proper action on a
    CAT(0) cube complex for m ≥ 2. Both are imported in
    `brin-thompson-mv-contains-a-distortion-element`.
  - So Farley's route for V (a proper cubical action, then the Haagerup
    property, then finite Kazhdan subgroups) cannot work verbatim.
  - Two routes remain (unreviewed):
    - A commensurated subset of an nV-set gives an action on a CAT(0) cube
      complex (Sageev), and every subgroup with property (T) fixes a vertex of
      it. Finiteness then needs only that every Kazhdan subgroup of every vertex
      stabilizer is finite, not properness. The V case has this shape
      (`fw-subgroups-of-eventually-similar-groups-virtually-embed`).
    - A proper affine isometric action on Hilbert space that is not cubical.
      Distortion does not forbid one: BS(1,2) is amenable, so a-T-menable, and
      contains a distortion element.
- Next target: find an nV-set with a commensurated subset whose vertex
  stabilizers have only finite Kazhdan subgroups, or build an infinite Kazhdan
  subgroup of 2V. Abstract twisted Brin–Thompson groups have property FW_∞
  (Fournier-Facio–Wu–Zaremsky, arXiv:2603.24687). This lane has not checked what
  that property excludes for classical nV.
- 2026-09-17 (swarm-0917-w2-zar-pull-1, operator-algebras lane): **exact
  reduction to orbit finiteness.**
  - Established: `finitely-generated-subgroups-of-nv-are-finite-iff-germ-finite`.
    A finitely generated `K ≤ nV` is finite iff offsets are bounded at each
    point, iff it has finitely many germs at each point, iff all orbits are
    finite and stabilizers act trivially near their fixed points.
  - The proof is a brick induction over words plus compactness.
  - For Kazhdan `K`, the finite-index stabilizers have finite abelianization.
    This kills the germ characters `Stab_K(x) → Z^n`, so finite orbits alone
    suffice.
  - Route `kazhdan-subgroups-of-nv-finite-from-finite-orbits` reduces this claim,
    with nothing lost, to `kazhdan-subgroups-of-nv-act-with-finite-orbits` (OPEN).
    Equivalently, `ℓ^2(Kx)` has almost invariant vectors for every `x`.
  - **Class removed.** Any construction of an infinite Kazhdan subgroup whose
    orbit Schreier graphs are all amenable fails at the orbit step. Such
    constructions include subgroups of the full-shift topological full group in
    2V. For these, Attempt (b)'s bandwidth and spectral-gap count is unnecessary.
  - **A counterexample needs** an orbit with a spectral gap on which the
    offsets, or the Busemann heights at aperiodic points, are unbounded.
  - **Dead end.** Invariant means on ambient nV-orbits (horocyclic-product
    Følner sets) only give *some* finite K-orbit per ambient orbit, not every
    orbit.
  - Operator-algebra framing:
    - `c|_K` is a class in `H^1(K, C(C^n, Z^n))`, with
      `C(C^n, Z) = K_0(C(C^n))`.
    - `K` is finite iff this class is a bounded coboundary.
    - Groupoid-level amenability of the Cuntz product groupoid carries no
      further information here, because it holds for every n and never enters
      the criterion.
- 2026-09-17 (lane swarm-0917-w2-zar-pull-2, transplanter via entropy-measure,
  unreviewed): **reduction to invariant measures on minimal sets.**
  - Established `kazhdan-subgroups-of-nv-finite-iff-invariant-sets-carry-measures`: a
    Kazhdan `K <= nV` is finite iff every minimal closed `K`-invariant subset of `C^n`
    carries an invariant probability measure. Unconditionally, every invariant
    probability measure of `K` lives on the open set `U_K` of points with a clopen
    neighbourhood fixed pointwise by a finite-index subgroup.
  - Mechanism: for an invariant measure `ν`, the slope cocycle is a 1-cocycle in the
    Koopman representation on `L^2(ν)^n`; (T) makes it an integer coboundary `F`;
    bricks of shape `c·1 + F(x)` with canonical charts give almost invariant vectors
    in `l^2` of the `K`-set of (clopen set, chart) pairs, and (T) forces finite orbits.
    This is the missing potential that repairs the shape-weighted families above.
  - New route `kazhdan-nv-finite-via-measured-minimal-sets` requires that criterion
    and the open claim `minimal-sets-of-kazhdan-subgroups-of-nv-carry-invariant-measures`,
    which is equivalent to this claim.
  - Dead ends, with the exact step: the Lebesgue half-density representation breaks
    the cocycle identity by the factor `2^{Σ s/2}`; the Navas-type current kernel
    `Π_i 1/μ_i(x_i ∧ y_i)` is not square integrable near the partial diagonals
    `{x_i = y_i}` for `n >= 2`; the skew product `C^n x Z^n` has only an infinite
    invariant measure, and normalizing it needs an invariant measure on `C^n`.
    Details in `research/artifacts/kazhdan-nv-measure-criterion-2026-09-17.md`.
  - Any proof of the remaining claim must use nV-structure: `SL_3(Z[1/p])` acts
    minimally on `P^2(Q_p)` with no invariant measure.
- 2026-09-17 (lane swarm-0917-w4-z-nv-kazhdan-subgroups, calibration, unreviewed):
  **rank-two word-system structure alone cannot prove this claim.**
  - Established (unreviewed) `rank-two-prefix-replacement-groups-contain-infinite-kazhdan`.
    It concerns a lattice `Γ` in `PGL_3(K)` (`K` nonarchimedean, characteristic zero)
    acting freely and type rotatingly on vertices. Such `Γ`:
    - is infinite and Kazhdan;
    - acts faithfully on its Robertson–Steger boundary `Ω`, each element by finitely
      many cylinder prefix replacements `ᾱ(p) ⇒ ᾱ(p')` of a finite rank-two word system
      satisfying (H0)–(H3), with `Z²` shape offsets;
    - has no invariant probability measure and no finite orbit.
  - The proof reads the prefix replacement property directly off Robertson–Steger's
    formula `φ(s_{w̄2,w̄1}) = γ1_{Ω(p1)}` and Lemma f2. Faithfulness comes from
    simplicity of `C(Ω)⋊Γ`, and the absence of measures from pure infiniteness.
  - **Class killed.** Proofs that use only that `K` is Kazhdan and acts by finitely many
    prefix replacements over a finite rank-two word system, with `Z²` offsets,
    irreducibility and pure infiniteness. Each such proof dies at the step "finite
    orbits" or "invariant measure on a minimal set". So
    `kazhdan-subgroups-of-nv-act-with-finite-orbits` and
    `minimal-sets-of-kazhdan-subgroups-of-nv-carry-invariant-measures` cannot be proved
    that way.
  - **The invariant that must enter** is the product factorization of nV's word
    system (`A = A_1 × A_2`, `M_1 = J⊗I`, `M_2 = I⊗J`): prefix replacement in one
    coordinate leaves the other coordinate's letters untouched. Rank one is below the
    threshold (SFT full groups have no infinite Kazhdan subgroup).
  - **Negation route (open).** If a Robertson–Steger rank-two full group, or just `Γ`,
    embeds in some nV, this claim is false.
    - The direct coding (an open subgroupoid embedding into `G_2^2` with constant
      offsets) needs the horizontal coding of consecutive rows to agree.
    - In Robertson–Steger systems rows are related by the (H1) squares, which act as a
      finite-state transducer. So that coding is expected to die at this step
      (heuristic, unproved).
    - Details in `research/artifacts/rank-two-prefix-replacement-kazhdan-2026-09-17.md`.
- 2026-09-18 (lane bh-free-38; unreviewed). **Literature check and a dead Haagerup
  route.**
  - **Literature: open.** arXiv API searches on "Brin-Thompson" together with
    Haagerup, a-T-menable, property (T) or Kazhdan, and on "Haagerup" with
    "Thompson", find no paper that settles the Haagerup property or (T) for nV,
    n ≥ 2. Brothier–Jones (arXiv:1805.02177) treat F, T and V. Hughes
    (arXiv:0804.0610) treats locally finitely determined groups of local
    similarities of compact ultrametric spaces. Zaremsky's arXiv listing has
    nothing on this question.
  - **The Hughes route is dead for n ≥ 2** (abstract read). Hughes proves that
    locally finitely determined groups of local similarities have the Haagerup
    property. Farley's appendix shows that his sufficient condition is equivalent
    to a proper action on a space with walls.
    - Properness on a discrete wall space passes to subgroups.
    - `brin-thompson-nv-no-cubical-action-proper-mod-triangular` (item 1, with
      trivial `H`), and Callard–Salo Cor 1.2 as imported in
      `brin-thompson-mv-contains-a-distortion-element`, exclude such an action
      for nV.
    - So for n ≥ 2, nV embeds in no Hughes group. Every Haagerup proof for nV
      must use a non-wall cnd function, as already recorded for the transversal
      half.
  - **Weaker targets that suffice for the BH test cases.** Deligne's lattices
    and the Torelli lower-central quotients `Q_{g,c}` (g ≥ 3, c ≥ 2) are excluded
    from every mV by either of two open statements, each weaker than this claim:
    - `kazhdan-subgroups-of-brin-thompson-groups-have-finite-center`. Each of
      these groups contains an infinite Kazhdan group with infinite center.
    - `heisenberg-group-embeds-in-no-brin-thompson-group`, via
      `deligne-lattices-and-torelli-quotients-contain-heisenberg-groups`.
