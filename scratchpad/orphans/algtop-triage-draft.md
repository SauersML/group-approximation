# AlgTop triage — 46 modules, pre-compile pass

Compile column is PENDING for all 46: the probe clone (`orph-algtop`) is still
being populated (lead reported 321/4600 oleans) and I have not run, and will
not run, another probe until told it's ready. One probe was already launched
before the hold instruction arrived; its log shows only the rsync line and the
`lake build ...` start banner, nothing past that — no result to report, and I
will not trust whatever it eventually prints without checking it built against
a complete clone.

This table is the no-compiler part: what each file claims, and the
by-content duplicate check (declaration-name index across the whole repo,
followed by hand-reading every real hit — not a title scan).

## Group 1: near-total 1:1 ports into CharClass (highest-confidence dead)

| Module | Claims | Duplicate check |
|---|---|---|
| ComplexProjectiveChart | Charts on ℂPᴺ: `sqNorm`, `chartVec`, `chartAt`, `chartHomeo`, homeomorphism onto the chart set | 30 of 34 declarations name-identical in `CharClass/ProjectiveSpaceChart.lean` |
| ComplexProjectiveCover | Two-chart cover of ℂPᴺ, base point, intersection | 12 of 12 declarations name-identical in `CharClass/ProjectiveSpaceTwoCover.lean` |
| ComplexProjectiveHyperplane | The hyperplane inclusion ℂP^{N-1} ↪ ℂPᴺ, `inclMat`, closed embedding | 17 of 19 declarations name-identical in `CharClass/ProjectiveSpaceHyperplane.lean` |
| ComplexProjectivePuncture | ℂP^{N+1} minus the base point, `scale`, `diagR`, `rad`, deformation retract data | 36 of 38 declarations name-identical in `CharClass/ProjectiveSpacePuncture.lean` |
| ComplexProjectivePunctureRetract | The retraction of the punctured space onto the hyperplane | 19 of 21 declarations name-identical in `CharClass/ProjectiveSpaceRetract.lean` |
| ComplexProjectiveSphere | ℂPᴺ minus hyperplane ≃ ℂᴺ via a chart, contractibility | 2 of 2 declarations name-identical in `CharClass/ProjectiveSpaceSphere.lean` |
| SteenrodCut | Combinatorics of Steenrod `⌣ᵢ`: cut sets `cutU`/`cutV` of a simplex's vertices | full-file read (both sides): `CharClass/SteenrodCut.lean` is a direct rewrite — generalizes `Fin (m+1)` to `Fin N`, adds `eq_faceOfFinset`; same docstring voice |
| CupProduct | Simplicial cup product on the singular cochain complex, cup with cocycles/coboundaries, descent to cohomology | its entire distinctive vocabulary (`cupRightMor`, `cupLeftFixedMor`, `cupRight_cocycle_cond`, `cupLeftFixed_cocycle_cond`, `cupLeftMor`, `cupHomologyLeft/Right`, 20 declarations total) is name-identical in `ThirdParty/HamSandwich/.../AlgebraicTopology/CohomologyCupProduct.lean` (reachable); a smaller overlapping API (`cup`, `cup_mk`, `cup_add_left`, `zero_cup`, `cup_zero`, `cup_one`) is also name-identical in `CharClass/CohomologyBasic.lean` — two independent, reachable reimplementations, neither of which imports this file |

**Superseded by**: `CharClass/ProjectiveSpace{Chart,TwoCover,Hyperplane,Puncture,Retract,Sphere}.lean`, `CharClass/SteenrodCut.lean`, `ThirdParty/HamSandwich/.../CohomologyCupProduct.lean`, and `CharClass/CohomologyBasic.lean` — all reachable, all landed by 2026-09-05 as part of either the "LIX characteristic-class layer" wiring (root commit `92e358f9d`) or the earlier, independently-successful HamSandwich cup-product development.

## Group 2: same role, disjoint or partly-disjoint vocabulary (the disguised case)

| Module | Claims | Duplicate check |
|---|---|---|
| CupAssoc | Associativity and left-unitality of the cup product, `cup_assoc`, `one_cup` | 12+ declarations (`cup_assoc`, `one_cup`, `frontFace_comp_frontFace`, ...) name-identical in `CharClass/CohomologyAssoc.lean` |
| ManuscriptSectionZeroCount | The manuscript's mapping-torus section vanishes at exactly one point, `manuscriptSection_eq_zero_iff` | **Zero name overlap** — but `CharClass/LemmaTwoZero.lean`'s own docstring states outright: "the same linear-algebra content as `AlgTop/ManuscriptSectionZeroCount.lean`'s `manuscriptSection_eq_zero_iff`, run in the clutched-circle model of S¹ instead of the raw [0,1] interval." Confirmed textually, invisible to any name scan. |
| ChernSeries, ChernMap | Total Chern class as a normalized, multiplicative power series; naturality under a coefficient ring map | `chernClass`, `chernClass_zero`, `chernClass_map` all name-identical in `CharClass/ChernRelation.lean` — **but the definitions differ**: `CharClass` uses Grothendieck's projective-bundle/Leray–Hirsch definition (`PowerBasis`/`minpolyGen`); `AlgTop` uses Newton-identity power series (`newtonSeries`). Same role (normalization, multiplicativity, naturality), different machinery. |
| CochainLeibniz | Alexander–Whitney Leibniz identity `δ(φ⌣ψ) = δφ⌣ψ ± φ⌣δψ` for **arbitrary commutative ring R** | **No name overlap**, but content overlap found by tracing an import, not a name: `ThirdParty/HamSandwich/.../AlexanderWhitneyChainMap.lean` proves `aw_cochain_leibniz_zmod2` — the same identity, specialized to `ZMod 2`. `CharClass/SteenrodCochain.lean` and `CharClass/SteenrodCut.lean` both import that file, confirming the corpus's actual Steenrod/cup-product machinery runs on the `ZMod 2` version, not this file's general-R one. |
| Kronecker | `Hⁿ(X;R) → Hom(Hₙ(X;R),R)` evaluation pairing, for arbitrary R, feeding a from-scratch UCT | **No name overlap**, content overlap found by reading, not grepping: `ThirdParty/HamSandwich/.../AlgebraicTopology/KroneckerTopClassAction.lean` and `KroneckerNaturality.lean` (reachable) build and use `kroneckerMap : Hⁿ(X;F₂) × Hₙ(X;F₂) → F₂`, the `ZMod 2`-specific instance of exactly this pairing, already landed. |

**Superseded by** (naming the exact declarations, per the request): the `ZMod 2` route through `AlexanderWhitneyChainMap.aw_cochain_leibniz_zmod2` / `kroneckerMap` / `CharClass.LemmaTwoStatement.false_of_stepC_stepD` — see Group 3 below for why the arbitrary-`R` generality these two files carry was never spent.

## Group 3: no name or content duplicate found, but the stated GOAL is superseded

Every file below states, in its own docstring, that it is lane `found-euler-class`
or `found-chern-classes`, campaign target 3 (STW Problem LIX), working toward
Lemma 2 or Lemma 3 of
`research/artifacts/stw59-simple-ah-k1-counterexample-manuscript-2026-09-05.md`,
via an **integral-cohomology-from-scratch + Newton's-identity-Chern-classes**
route. I checked whether that route's endpoint is still needed: it is not.
`CharClass/LemmaTwoStatement.lean`'s `false_of_stepC_stepD` (Steps A/C/D, landed
2026-09-05 20:05–20:28, same day, later) closes Lemma 2 entirely inside `ZMod 2`
cohomology on a clutched-circle model of S¹ — no integral cohomology, no
universal coefficient theorem, no Kronecker pairing, no cross products, no
Newton's identity anywhere in that route (checked: zero `powerSum` hits in
`CharClass/`). This is "genuinely superseded" in the sense the assignment asks
for — a named replacement exists — but it is a different KIND of supersession
than Group 1: no individual declaration here is duplicated, the *role* is.

| Module | Claims |
|---|---|
| ChernPowerSums | Newton's-identity power-sum machinery for total Chern classes (`newtonSeries`, `chernChar`) |
| ChernLineRoots | Chern roots of a line bundle sum via the power-sum series |
| ChernNewtonIdentity | `chernChar`, `factorial_mul_chernChar` — Newton's identity itself |
| ChernNewtonDischarge | Discharges `hlow` (LIX Lemma 3) from Newton's identity alone |
| ChernNewtonSquareZero | Chern classes under a square-zero hypothesis on the coefficient ideal |
| ChernParityCoefficient | Parity of `binom(k+2-i, i)`-style coefficients feeding the Newton computation |
| ChernPolynomialModel | A worked instantiation of the Chern-power-sum layer at `MvPolynomial` |
| ChernSplitNewton | Newton's identity for a split (sum-of-lines) bundle |
| ChernSquareZeroIdeal | Pure commutative-algebra lemmas about square-zero ideals, feeding `ChernNewtonSquareZero` |
| ChernEvenTopClass | Vanishing of `chernClass_prod_line_pow` above a degree bound |
| MappingTorusParity | Lemma 3's parity statement: `even_chernClass_top_pairing_of_sumLine` |
| MappingTorusParityCore | The bare-sequence parity core of Lemma 3, depending on nothing but Mathlib |
| MappingTorusSectionZeros | The manuscript's mapping-torus section's zero locus, on the raw `[0,1]` model |
| EulerLocalModel | The transverse local model at the mapping-torus zero (Euler-class computation) |
| EulerParityBridge | States exactly what closes Lemma 2: zero-count parity vs. Chern-pairing parity |
| WuBinomialGap | The odd-binomial-coefficient gap in the Wu-formula tower induction for Lemma 3's mod-2 route |
| OddDegreeOfHomeomorphism | A self-homeomorphism of a sphere has odd degree — the piece "nobody owns" per `EulerParityBridge` |
| SingularCohomology | Element-level integral (arbitrary-R) singular cohomology API, generalizing the vendored `ZMod 2`-only development |
| Spheres | Integral cohomology generator of Sⁿ and the top-degree pairing, via the Kronecker/UCT route |
| UniversalCoefficients | The UCT itself: Kronecker map surjective always, injective when `Hₙ₋₁` is projective |
| CrossProduct | External cross product in singular cohomology, naming generators of `H^*(S¹×S⁵×∏ℂP^{d_j})` |
| SingularChainFree | Singular chains are free and cycles are a direct summand (bridge from `FreeSubmodulePID` to UCT) |
| FreeSubmodulePID | Submodules of free modules over a PID are free at **arbitrary** (not just finite) rank — Mathlib only has the finite-rank case. Pure algebra, no topology. Checked for a duplicate anywhere else in the repo: none found. |
| EvenCohomologyRing | The even-degree subring of `H^*(X;R)`, reindexed, as the ring Chern classes live in | *(possible role-overlap with `CharClass`'s `ParityEven*` cluster — not confirmed by declaration content, flagging as unresolved rather than asserting)* |
| ComplexProjectiveProduct | Products `∏ⱼ ℂP^{d_j}` and their point-set properties, feeding the from-scratch cohomology computation of the base space `Y` | No CharClass file for a "product of projective spaces" found; may simply be unneeded now that `Y`'s cohomology is computed the `ZMod 2`/clutched-circle way |
| CupCommutativitySign | The sign of vertex-reversal, `revSign n = (-1)^{n(n+1)/2}`, for graded commutativity of the cup product | No duplicate found anywhere in the repo by name or by a targeted search for `revSign`/`vertexReversal` |

## Group 4: different purpose entirely, likely "compiles and is wanted"

| Module | Claims | Why not superseded |
|---|---|---|
| BundleCalculusProjection ("Bundle calculus I") | Projections up to unitary conjugation; homotopy invariance of a preconnected family | same finding as the row below — part of one 6-file cluster, no duplicate found |
| BundleCalculusTransport ("Bundle calculus II") | Orders the section algebra as a `StarOrderedRing`; transport along the model | same finding as the row below |
| BundleCalculusPullback ("Bundle calculus III") | Pullback of a bundle along a continuous base map, and its homotopy invariance | same finding as the row below |
| BundleCalculusInvariant ("Bundle calculus IV") | Every unitary-conjugation-invariant numerical invariant is a homotopy invariant | A projection-picture theory of vector bundles over C\*-algebras. These six serve the **K-theory** campaign, not the characteristic-class one. `BundleCalculusModelBridge.lean`'s own docstring names `KTheory/MatrixProjection.lean` and `KTheory/Functorial.lean` as the consumers of its ambient model. Checked directly: **neither KTheory file currently imports any BundleCalculus file** — real, unconnected infrastructure with a named intended consumer, not a duplicate of anything. `KTheory.Basic`/`Functorial` are themselves confirmed compiling (separate orphan-sweep build-test) but still unwired. |
| BundleCalculusModelBridge ("Bundle calculus V") | The two ambient models (`Matrix ι ι C(X,ℂ)` and the section algebra) are one algebra | same finding as the row above |
| BundleCalculusUnitSection ("Bundle calculus VI") | A nowhere-vanishing section splits a trivial line off a projection, unstably | same finding as the row above |

## What's still open

- All compile status: **PENDING**, waiting for the lead's ready signal on `orph-algtop`.
- `EvenCohomologyRing`'s possible overlap with `CharClass/ParityEven*` — flagged unresolved, not asserted either way.
- Whether `ComplexProjectiveProduct`'s "product of projective spaces" fact is needed anywhere in the landed corpus — no consumer found, but I did not exhaustively rule out a differently-shaped equivalent.
