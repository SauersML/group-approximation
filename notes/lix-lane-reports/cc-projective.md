# Lane `cc-projective`

Ownership: `GroupApproximation/CharClass/{ProjectiveSpace*,LerayHirsch*,Chern*}.lean`,
namespace `GroupApproximation.CharClass` (new declarations in the sub-namespaces
`LH`, `CPn`, `Gysin`).

Probe: `bash scratchpad/cc/ccprobe.sh cc-projective GroupApproximation.CharClass.<Module>`.

## GREEN (job counts from the last probe of each)

Point-set chain and the additive computation

* `ProjectiveSpaceBasic/Chart/Hyperplane/Puncture/Retract/TwoCover/Sphere` — the
  point-set chain, re-proved from the paused fleet's red `AlgTop/ComplexProjective*`.
* `ProjectiveSpaceCover` — `CPtop`, the two opens, contractibility of the chart,
  the two homotopy equivalences.
* `ProjectiveSpaceCohomology` — `MVSequence`, `bijective_resV`, `bijective_delta`,
  `HasPointCohomology`, `HasSphereCohomology`, `HasCPCohomology`,
  `hasCPCohomology_succ`.
* `ProjectiveSpaceSymmetry` (8676) — `PathConnectedSpace (CP d)`.
* `ProjectiveSpaceHomogeneous` (8659) — `exists_homeomorph_mapsTo_basePoint`, for cc-thom.
* `ProjectiveSpaceInputs` (8784) — the three cover pieces with their cohomology.
* `ProjectiveSpaceComputation` (8789) — **item 1**, `hasCPCohomology_CP`, unconditional.
* `ProjectiveSpaceStable` (8803) — **item 1, second half**: `pull_cpIncl_cpGen`, the
  hyperplane inclusion carries the degree-2 generator to the degree-2 generator.
* `ProjectiveSpaceRing` — `lineGen`, `cupPowE`, `GysinSequence`, `cupPowE_ne_zero`.

The Leray-Hirsch ladder

* `LerayHirschAlgebra` — `bijective_of_ladder` (the five lemma in element form;
  Mathlib has none at this pin), `powerBasisOfBijective`.
* `LerayHirschDegree` (8783) — `lhDomainCard`, `lhMap`, `LerayHirschGraded`, `gamma`.
* `LerayHirschColumn` (2056) — `MVFacts`, `lhDomain`, the five componentwise maps.
* `LerayHirschSquares` (2058) — `MVPulls`, `MVLadder`, `lhSum`, `lhSum_pull` (all four
  restriction squares at once), `lhSum_delta`, and the column's three exactness
  statements.
* `LerayHirschInduction` (2454) — `bijective_lhSum`, the Mayer-Vietoris step, by the
  five lemma, with degree zero done by hand as the four lemma.
* `LerayHirschBridge` (2456) — `lerayHirschGraded_of_bijective`, the ladder's output in
  the published interface, and the way back in.
* `LerayHirschMV` (8792) — **every ladder hypothesis discharged**;
  `bijective_lhSum_comap` carries none.
* `LerayHirschTransport` (2457) — moving the theorem across an isomorphism.
* `LerayHirschHomotopy` (2883) — the same over a square that commutes only in
  cohomology, which is what a contractible open set gives.
* `LerayHirschRel` (8796) — an open set viewed inside a larger one; every lemma
  is `rfl`.
* `LerayHirschCover` (8797) — `LHOver`, and the two-set step relativized.
* `LerayHirschFinite` (8798) — **Leray-Hirsch over a finite cover**.
* `LerayHirschPoint` (8744) — **the base case**, over a base with the cohomology
  of a point.
* `LerayHirschBase` (8745) — the base case over bundled hypotheses, and the
  rank-two case, which needs no ring structure.
* `ProjectiveSpaceCharts` (8665) — the `d+1` standard charts: open, contractible,
  and they cover.
* `LerayHirschUnion` (8810) — a cover recognised as a fold, and the chart cover of
  `ℂP^d` in that shape.
* `LerayHirschChart` (8835) — odd-degree vanishing for `ℂP^d`, `H^3 = 0` for
  cc-wu, and `LHOver_of_chart`, the base case over a trivialising open.
* `GysinFromGraded` (2459) — the two `GysinData` fields read off
  `LerayHirschGraded` at rank two.
* `LerayHirschBundle` (8846) — **Leray-Hirsch for a bundle over a compact base**,
  over one hypothesis, plus `noOddCohomology_baseY`.
* `ProjectiveSpaceInterVanish` (8836) — the cover's intersection carries no
  positive even classes, so every positive power of the tautological class dies
  there.
* `ChernEulerSqOne` (8855) — `Sq^1` kills an Euler class, which is cc-wu's
  `sq_one_root`.
* `ProjectiveSpaceIterate` (8804) — the iterated hyperplane inclusion and
  generator stability along it.
* `ProjectiveSpacePerm` (8812) — permuting homogeneous coordinates fixes the
  degree-two generator.
* `LerayHirschRankTwo` (8800) — **the interface a Kunneth statement must supply**:
  three elementary hypotheses, no cover, no bundle, no projective space.

Chern classes and the Euler class

* `ChernRelation` (8686) — the Grothendieck relation as pure algebra.
* `ChernTotalRing` (2464) — the FULL graded mod-2 ring, `TotalH`.
* `ChernClasses` (2466) — `LerayHirschData`, `chern`, `chernPolynomial`.
* `ChernEuler`, `ChernEulerBundle` (8799) — **item 2**, `eulerOfBundle` and naturality.
* `GysinCover` (3343), `GysinFromLerayHirsch` (2057) — the Gysin sequence reduced to
  Leray-Hirsch for a rank-two bundle.
* `ChernEulerCastSucc` (8822) — the first-block coordinate inclusion fixes the
  degree-two generator.  `Fin.castSucc` lands in `Fin (d+1+1)` on the nose, where
  `iterMat` would land in `Fin (1+d+1)`; cc-bundle's `coordIncl_finRotate_mul_castSucc`
  compares it with the shift, and the topological half is the unitary-conjugation
  argument (homeomorphism, so bijective on `H^2`, and `H^2` is a line).
* `ChernEulerIndex` (8825) — **the Euler class across index sizes**.  For an arbitrary
  finite index the class is defined by pushing into a `Fin`; the injection and the
  representative are immaterial (`eulerOfBundle_pushforward_congr`), and pushing an
  already-`Fin` bundle along `iterFin` returns its own class
  (`eulerOfBundle_pushforward_iterFin`).  `eulerOfBundle_pushforward_eq_of_bundleIso`
  is the workhorse.
* `LerayHirschChartClass` (8887) — **the class identification**, and with it
  `LHOver_two_chart_of_trivialization`, the chart step with nothing left open.
  `tautEuler p` is the class `ξ`.  Every transport is `rfl`.
* `LerayHirschPlusOneClosed` (8892) — **Leray–Hirsch for `P(L ⊕ 1)`, unconditional**.
  `H^*(P(L ⊕ 1))` is free over `H^*(X)` on `1` and the Euler class of the
  tautological line, any line bundle, any base, no compactness.  Item 3, first half.
* `GysinRanged` (2058) — the Gysin step at one degree, hypotheses named rather than
  bundled.  `GysinData.pair_bijective` asks for every degree and is *false* for this
  bundle; the proof only ever used degrees `2` through `2d`.
* `GysinSphere` (8792) — `unitVectors (Fin (d+1))` has the cohomology of `S^{2d+1}`,
  for every `d`, in five lines.  Route through the *punctured* space, not the sphere:
  the `WithLp` seam is then crossed by a linear equivalence that need only preserve
  being nonzero.  The 153-line `n = 3` isometry in `LIXStepESphereModel` is avoidable.
* `GysinPairTaut` (8810) — **the pair condition in the Gysin range**, `2m+2` for
  `m < d`.  It genuinely fails at both ends.
* `GysinRetract` (8822) — the two pieces retract onto the base, and both readings are
  sections of the projection.  The hypothesis is `rfl` on each side.  Note that the
  complement retracts onto `P(p)`, not onto the base; they agree only at rank one.
* `GysinPairRetract` (8835) — the pair condition transported to those two readings.
* `GysinTautFields` (8896) — the tautological class on the two pieces.  It dies on the
  chart; on the complement nothing is computed, and that is the trick.
* `ProjectiveSpaceRingBootstrap` (8913) — **the ring**, from the Gysin sequence.
* `ProjectiveSpaceRingClosed` (8914) — **`CPGenHyp` and the frozen interface,
  unconditionally**.  Items 1, 2 and the ring of §1.4 item 3 are closed.
* `ChernWhitneyFlag` (8866) — **Whitney on the flag bundle**, `cc-wu`'s last
  `SplittingData` field.  Stated as an identity of polynomials, at which point there
  is no geometry in it: Chern classes are coefficients, pullback maps coefficients,
  and Vieta reads a product of linear factors.  Holds for every `k`, since both sides
  vanish above the rank for two different reasons.
* `LerayHirschShiftTerm` (2066) — the index shift, in two forms.  See TRAPS: the
  natural `lhTerm` statement is a `whnf` loop in the *statement*, not the proof.
* `LerayHirschPeel` (8808) — **the ladder's spanning half**.  Every class is a
  column, every degree, every rank, over two named hypotheses.
* `LerayHirschPeelCP` (8920) — `HasPeel` discharged against `cc-cohom-api`'s
  `cpSplit_closed`, with no cast.
* `LerayHirschPeelClosed` (8922) — **the spanning half, unconditional**.  Their
  `lhLow_general` discharged the floor, also with no cast.
* `LerayHirschColumnPack` (8923) — `HasFreeTuple`, the free-module statement in the
  producer's vocabulary, repackaged into the column shape `LHOver` consumes.
* `LerayHirschLadder` (8924) — **the ladder at general rank**, over `HasFreeTuple`.
* `LerayHirschTowerBridge` (2067) — a summand of `cc-cohom-api`'s Horner tower,
  written as a column term at the reflected index.  Their coefficient degrees grow
  with the index and the power shrinks; `lhTerm` is the other way round.  Neither
  convention is free, so the reindex lives here.  One lemma, four rewrites.
* `LerayHirschTowerSum` (8923) — **the tower expanded into the column sum**, by
  induction on its length, against their definition as landed.  Uses the *right*-handed
  shift, which needs no transport on the ambient degree at all: `cup _ ξ` already lands
  in `m + 2`.  Indexed by `Fin (k+1)`, not `range (k+1)` — see TRAPS.
* `LerayHirschChartGeneral` (8924) — **the chart step at any rank**.  The transport
  never cared about the rank; only the rank-two product instance did.
* `LerayHirschChartBundleGen` (8925) — the same for a projectivised bundle, over a
  local trivialisation.  The square over the base is `rfl` again.
* `LerayHirschChartClassGen` (8926) — **the class identification at general rank**,
  over `cc-bundle`'s rank-`r` tautological-line isomorphism.

## AUTHORED-UNVERIFIED

None.  Everything in the lane is probed green and pushed.

## NEEDS

0. **Nothing.**  cc-bundle landed all three facts (`BundleTautPieces`), the ring is
   unconditional, and `cc-cohom-api` has been told the commit (8c80f2e07).

   The general "Euler class is independent of the coordinate embedding" statement that
   stood in NEEDS item 1 below is **no longer needed** and should be considered
   withdrawn.  Identifying the Gysin class with the generator up front would have
   required it; running the argument against whatever class the construction produces
   proves that class nonzero in its own first power, and `H²` is a line, so the
   identification is free.

   Remaining in the lane, none of it blocked: §1.4 item 4 (Leray–Hirsch at higher
   rank, Künneth with `ℂP^n` and finite products) and the slice class.  Item 5's
   Whitney field is done; what `cc-wu` still needs from a *geometric* source is the
   flag bundle itself, namely a Leray–Hirsch instance on it and the split form of the
   relation, and that is item 4's business.

1. **cc-bundle, to close item 2.**  A general isometric embedding of projective spaces
   is essential on `H^2`.  Three statements, sent with the shapes: composition of
   `cpEmbed`s, the one-step shift as a `cpEmbed`, and independence of the embedding.
   I offered to take the first two myself.

2. **Nothing else is blocked on a peer.**  Both of the two facts I was waiting on,
   `MVDelta.mvDelta_cup` and `MVDelta.mvDelta_naturality`, have landed.

## THE STATE, AND THE ONE THING LEFT

The bootstrap is green above and below the class identification, and the class
enters at exactly one place.

Above it: `lerayHirschGraded_of_diagCover` (no compactness; the diagonal sets of a
projection of trace one cover, and are finite because the index type is),
`LHOver_two_chart` (the chart step, geometry fully discharged),
`lerayHirschGraded_plusOne` (the whole cover induction, over the class as a
parameter).

Below it: `ProjectiveSpaceRingGysin` takes a `GysinData` for the tautological line
to the ring, and `cpGenHyp_of_gysin` carries that to cc-cohom-api's generation
hypothesis.  `GysinPair.bijective_resPair` is the Mayer-Vietoris half of the
Gysin step.

**The one thing left is Euler-class naturality ACROSS INDEX SIZES.**  Over a chart
the tautological line of the projectivised sum is indexed by size `d+2` and the
pullback of the projective line's tautological bundle by size `2`; `BundleIso`
allows that, and must, because the same line sits in spaces of different
dimensions.  `eulerOfBundle_eq_of_bundleIso` requires a common index, so it does
not apply.  The fix is the rotation with two embeddings of different domains,
which is cc-bundle's; the generator half is `pull_cpBlockInclIter_cpGen` and is
green.

I should have seen this when I first wrote the four-field chart interface: the
index sizes were visible in `tautLineIsoCPOne`'s type.  I read it as an
isomorphism and did not read the indices.

## THE CROSS-LANE RULE, EARNED FIVE TIMES

Every cross-lane friction in this lane has been an index or a subtype written at
the producer's convenience rather than the consumer's, and every one dissolved
when the PRODUCER restated rather than when the consumer cast.  cc-bundle's
sharpening is the right statement of why: the producer already has the supporting
suite at an arbitrary index, so restating costs a few lines, whereas the consumer
would build a cast layer that then propagates through every later step.  The tell
that the direction was right is that the resulting transports are `rfl`.

## THE CIRCULARITY, AND WHERE IT IS BROKEN

Worth recording, because two lanes hit it from opposite sides on the same day.

The Kunneth in the form Leray-Hirsch consumes, freeness on POWERS of the
degree-two class, is at a point exactly the ring structure of `H^*(CP^d)`: at the
top degree, bijectivity says the top power is nonzero.  So it cannot be proved by
Mayer-Vietoris on the chart-and-puncture cover, which is silent about the top
power.  cc-cohom-api reached the same wall from their side: flatness and
surjectivity are one problem, and chasing it further returns to the Kunneth's own
injectivity.  Three routes, one circle.

It is broken from OUTSIDE, at rank two, where the change of basis between the
connecting-map class and the tautological class is triangular and costs nothing.
That gives rank-two Leray-Hirsch with no ring structure, hence Gysin, hence the
ring; and with the ring the same triangular argument works at every rank.

## THE CHAIN IS ONE THEOREM DEEP

`lerayHirschGraded_of_trivializing_cover` gives Leray-Hirsch for a
projection-model bundle over a compact base from a single hypothesis: the theorem
over one trivialising open.  The trivialising sets are open and cover, compactness
makes the cover finite, and the predicate "contained in a trivialising set" is
closed under intersection with anything, which is what the induction demands and
what a trivialisation supplies for free.

That hypothesis is cc-cohom-api's projective-factor Kunneth over an arbitrary
base, read through cc-bundle's chart trivialisation.  It is assigned and it is
the only thing between here and the mapping-torus instance that cc-thom's `su`
and cc-lix-odd's Chern-class parameter wait on.

**A correction to my own earlier bootstrap, worth keeping.**  I had argued the
Gysin route could run on the standard charts because those are contractible.
That is not sufficient, and the reason is the induction rather than the charts:
its predicate must be closed under intersection with an arbitrary open, so it
produces intersections of a chart with arbitrary opens, which are still
trivialising but not contractible.  So the Kunneth over an arbitrary base is
needed even for the projective-space case.

## WHAT IS LEFT

The Leray-Hirsch machine is complete end to end: base case over a point,
transport to a trivialising open set, the two-set Mayer-Vietoris step, the finite
cover induction, and the bridge to the published `LerayHirschGraded`.  Producing
an actual instance now needs only bundle-side geometry, not cohomology.  For the
Gysin bootstrap the base side of that is DONE: the `d+1` standard charts of
`CP^d` are built, shown open and contractible, shown to cover, and packaged in
the fold shape the induction consumes.  What is left is one bundle fact, which is
cc-bundle's: the tautological line is trivial over each chart, and `P(taut + 1)`
over a chart is that chart times `CP^1`.

## THE ONE REMAINING MATHEMATICAL GATE, and why

Leray-Hirsch is complete except for its BASE CASE: the theorem over an open set on
which the bundle is trivial.  The base case is not a corollary of the ladder, and the
order it has to be built in is forced by one fact that is worth recording because it
looks like an obstruction and is not:

**The Mayer-Vietoris cover of `CP^n` by the chart and the punctured space cannot see
the top power of the generator.**  Restriction to the punctured space is injective only
up to degree `2n-2`, so it gives `h^m` nonzero for `m` at most `n-1` and says nothing
about `h^n`.  In `CP^2` the restriction sends `h` to the generator of `H^2(S^2)` and
`h^2` into `H^4(S^2) = 0`.  So the ring structure genuinely needs the Gysin sequence,
exactly as the program note says, and no amount of work on the additive side will
produce it.

The bootstrap that closes it, in order:

1. The finite-cover induction, relativized to an open base.  DONE.
2. The standard `n+1` charts of `CP^n`: contractible, and the tautological line is
   trivial over each.
3. Over each chart, `P(taut + 1)` is `chart x CP^1`, and Leray-Hirsch there needs only
   the ADDITIVE structure of `H^*(CP^1)`, since `h^2 = 0` there.  No circularity.
4. The cover induction then gives Leray-Hirsch for `P(taut + 1)` over `CP^n`, hence the
   Gysin sequence, hence the ring `F2[h]/(h^(n+1))`.
5. With the ring in hand, the Kunneth for a `CP` factor follows by induction on the
   fibre dimension: `delta_cup` moves the sphere generator across the connecting map and
   `delta_naturality` identifies its image with `xi^(d+1)`.  Both are now theorems.
6. General Leray-Hirsch base cases over contractible trivialising opens then reduce to
   the ring structure, and the machine is closed.

## TRAPS

* **Solving for an index size is a truncated subtraction, so the application times out
  rather than failing to typecheck.**  Applying the index-crossing Euler workhorse needs
  `a + k + 1` to be the class's own index size; `k := N - a` makes that true only
  propositionally, and the application is an `isDefEq` timeout.  The fix is a variant
  taking the common size as an equation and discharging it by `subst`.  Third member of
  the family, after the `whnf`-in-the-statement and `range`-binder traps.

* **A `Finset.range` binder cannot carry an index bound, and the summand then fails to
  *elaborate*.**  The reflected index `k - i` is truncated subtraction, so a cast on the
  coefficient's degree is valid only under `i ≤ k`.  With `∑ i ∈ Finset.range (k+1)` the
  summand is a function of every natural `i`, the cast has no hypothesis, and the
  statement is rejected.  `∑ i : Fin (k+1)` puts `i.2` in scope in the binder.  Same
  family as the `whnf`-loop-in-the-statement trap: the cost is elaboration, not proof.
* **Right-handed shifts are cheaper than left-handed ones.**  `cup x ξ` lands in `m + 2`
  on the nose, so raising a column index by one on the right needs no ambient cast; on
  the left it needs `cup_comm` and a transport.  `cupPowE_succ` is already right-handed.

* `sInclusion` applied to an open set coerced to a set leaves its source type a
  metavariable, which will not unify with a space whose subtype came from the `SetLike`
  coercion on `Opens`.  Write the inclusion as `TopCat.ofHom` with the expected type
  given.
* `pull_congr (subInclusion_comp_sInclusion _)` cannot synthesize the subset proof; pin
  it with `(s := _) (t := _)`.
* `MVFacts` is a Prop-valued structure, so its instance is a `theorem`, not a `def`.
  Lean says so explicitly, which is the only reason it is cheap to find.
* Proofs inside an anonymous constructor are stated against unreduced applications, so
  `rw` cannot see the component until `dsimp only` has beta-reduced it.  Building a
  homomorphism as a `comp` of a Pi-level homomorphism with `AddSubgroup.subtype`, or as
  an `AddMonoidHom.codRestrict`, avoids the problem entirely and is what the ladder does.
* A section `variable` is not in scope in a statement that does not mention it, so a
  structure argument that only the PROOF uses must be explicit.
* Truncated subtraction: `0 - 2 * i` does not reduce to `0` for a variable `i`, so a
  degree-zero component still needs a `cohCast`.
* A class whose degree is written as a SUM handed to a lemma stated at a literal
  is not a cheap unification: it is a deterministic `isDefEq` timeout.  State the
  lemma at an arbitrary degree with the side condition as a hypothesis.  `Sq^1` of
  a degree-two class has degree `1 + 2`, which is where this bites.
* A `have` whose statement mentions the coercion of a `Fin` literal gets that
  coercion reduced during elaboration, so a rewrite phrased with the unreduced
  form does not match; reach it through `show` instead.
* `Homeomorph.contractibleSpace` transports contractibility from the TARGET to
  the source, so the homeomorphism is used without `.symm`.
* Landing: check a peer's file with `git show origin/main:<path>`, never the
  working tree, since plumbing pushes leave the shared checkout behind.  When the
  ordinary flow is blocked, build the commit against the fetched tip with a
  TEMPORARY index, gate on the changed-path list, and diff the pushed blob
  afterwards; that diff is the only proof of what landed.

## 2026-09-06 — ITEM 5's SLICE HALF IS CLOSED

* `ChernSliceNaturality` (cf1f83b6a, **PROBE GREEN, 9148 jobs**) — naturality of
  the mod-2 Chern classes, and `KnTwo.ChernSliceNatural` as its instance.

Four named results, in the order they depend on each other:

* `LH.chern_map_of_square` — **naturality with no topology in it**.  Given two
  `LerayHirschData`, a map `f` of base rings and a map `g` of total rings with
  `g ∘ π^* = π'^* ∘ f`, `g ξ = ξ'` and equal ranks, `D'.chern k = f (D.chern k)`.
  The proof is `chernPoly_map`: the image of the defining relation is a monic
  relation of the right degree for the new generator, and uniqueness identifies
  it with the new relation.
* `LH.projComap_square` — `cmap (projComap f q) ≫ projMapOf q =
  projMapOf (comap f q) ≫ cmap f`, by `TopCat.Hom.ext` and `rfl`.  In the
  projection model `P(f^*E)` *is* the fibre product, so there is nothing to prove.
* `LH.tautEulerOf_comap` — `pull (cmap (projComap f q)) 2 (tautEulerOf q) =
  tautEulerOf (comap f q)`, one application of `eulerOfBundle_comap`.  The
  pushforward of the tautological line commutes with the base change *definitionally*:
  both sides are `fun z => coordIncl e * z.val.2 * (coordIncl e)ᴴ`.
* `LH.chern_comap` — the three assembled, over compact non-empty bases.
* `LH.chernOf q s hs hs1 k : Hmod2 (TopCat.of X) (2 * k)` — the classes in their
  own degrees, for a bundle of constant rank `s ≥ 1`.
* `LH.chernSliceNatural_chernOf` — `KnTwo.ChernSliceNatural Y p5 p1
  (chernOf q s hs hs1) (chernOf (comap (nSliceMap Y p5 p1) q) s _ hs1)`, for any
  `q : Bundle (KnTwo.torusBase Y) ι` of constant rank `s ≥ 1` over a compact
  non-empty `Y`.  Also `LH.nSliceMap` and `LH.cmap_nSliceMap`, which present
  `KnTwo.nSlice` as a `C(Y, torusBase Y)` so that `Bundle.comap` can eat it, and
  the instance `LH.nonemptySphere`.

### Why this cost two probes and not six

The scoping said `chernClass_map` needs only two power bases, a ring map, equal
ranks and a pulled-back relation — **no fibre product**.  That was right, and it
is the whole reason the file is short.  The temptation was to prove that
`P(f^*E) ≅ P(E) ×_X Y` and then transport; that theorem is true, is much harder,
and is never needed, because the only thing the Chern classes see is the square
of rings.

### TRAPS from this file

* `trace_pushforward_one` lives in `CPn`, not in `Bundle`, even though every
  other name in the same expression is `Bundle`'s.  `autoImplicit false` reports
  it as an unknown identifier rather than as a missing open, which is the good
  case; qualify it rather than opening `CPn` wholesale.
* `ext` on an equality of `TopCat` morphisms into a product of SPHERES keeps
  splitting past the point of the proof, all the way into `EuclideanSpace`
  coordinates, and leaves two `.ofLp` goals that `rfl` will not close because the
  split has destroyed the shared head.  Stop it by hand:
  `apply TopCat.Hom.ext; exact ContinuousMap.ext fun _ => rfl`.
* `LerayHirschData.algebra` is a `def`, not an instance, so every lemma about
  power bases has to be `@`-pinned — unless you `letI := D.algebra` first, after
  which `chernClass_map D.powerBasis D'.powerBasis ...` needs no `@` at all: the
  two power bases are explicit arguments and their types pin every instance by
  unification.  `rw` still cannot cross between the `letI` fvar and `D.algebra`,
  so state the intermediate `have`s in the `letI` form and let `exact` do the
  final defeq.

## 2026-09-06 — THE SAME NATURALITY, AT THE MODEL THE CLASSES LIVE ON

* `LIXChernSlice` (8c7a0e1e5, **PROBE GREEN, 9154 jobs**) — `lixChern` is natural
  along `cc-cohom-api`'s `lixSlice`.

```lean
theorem pull_lixChern_lixSlice (dd : Fin ℓ → ℕ) (p1 : ↥sphereOne)
    (q5 : ↥(unitVectors (Fin 3))) (P : LixFamily dd) (hcont : Continuous P)
    (hproj : ∀ p, IsStarProjection (P p)) (s : ℕ) (hs1 : 1 ≤ s)
    (hs : ∀ x, (⟨P, hcont, hproj⟩ :
      Bundle (↥sphereOne × baseM dd) (VIdx dd ⊕ VIdx dd)).rank x = s) (k : ℕ) :
    pull (lixSlice dd p1 q5) (2 * k) (lixChern dd P hcont hproj k)
      = LH.chernOf (comap (lixSliceMap dd p1 q5)
          (⟨P, hcont, hproj⟩ :
            Bundle (↥sphereOne × baseM dd) (VIdx dd ⊕ VIdx dd))) s
          (fun y => hs (lixSliceMap dd p1 q5 y)) hs1 k
```

Also `lixSliceMap`, the same slice as a `C(baseY dd, ↥sphereOne × baseM dd)`,
which is the shape `Bundle.comap` eats, and `cmap_lixSliceMap`, which is `rfl`.

The proof is two steps and no new mathematics: `lixChern_eq_of_rank` takes the
branch that the constant-rank hypothesis names, and `LH.chern_comap` — proved
generically the same day — does the rest.  That the generic statement was proved
at an ARBITRARY map of compact non-empty bases rather than at the slice is the
whole reason this file is thirty lines.

### TRAP: `rw` closes with `with_reducible rfl`, and `lixN` is a plain `def`

The last step of `h2` left a goal whose two sides PRINT IDENTICALLY and which
`rw` refused to close.  The cause is not the printed terms: `rw` finishes with
`with_reducible rfl`, so a `def` that is not `@[reducible]` — here `lixN`, and
also the hidden `LerayHirschGraded` proof terms — is not unfolded.  A bare `rfl`
on the next line closes it at default transparency.  The tell is an unsolved
goal displayed as `X = X`; do not go looking for a real mismatch.

## 2026-09-06 — hnat, the S field, and the seam audit

* `LIXChernSliceNatural` (a501b49a1, **PROBE GREEN, 9155 jobs**) — `hnat`.
* `LIXChernSplit` (1a6884b8a, **PROBE GREEN, 9156 jobs**) — the `S` field.

`chernSliceNatural_lixChern` discharges `hslice_of_props`'s naturality hypothesis
WITHOUT transporting the bundle across `Wu.lixIso`.  The assigned route was to
carry the bundle to the other model and use the naturality proved there; that is
unnecessary, because `pull_nSlice_lixIso` already says the composite restriction
IS restriction along `lixSlice`, and `pull_lixChern_lixSlice` is stated exactly
there.  One composition, no bundle crosses the isomorphism.

`lixChernSplit` closes one of the three inputs `LemmaTwoStepDLix` records as
open.  `S` was never open: `Wu.chernSplitOfGraded` builds it from the degree
concentration alone, and `lixChernOf_mappingTorus` supplies that on a mapping
torus with the proof arguments already right.  Two remain, `hu` and `hne`, both
Thom-class facts.

### The seam audit, its findings, and its one wrong line

Two seams clean (the class type needs no coercion, since `Hmod2` is an abbrev
for `cohomologyZMod2`; every object at Step C is at `2 * lixRank dd`, with no
r versus r+1 anywhere at that seam).  Four instantiation constraints.  Two real
mismatches:

* `ThomChainThom.hne` is `sRel.hom u ≠ 0` while `lix_topClass_ne_zero_of_named`
  asks only `u ≠ 0`.  The structure's field is strictly stronger, so the
  structure builds the theorem and the theorem does not build the structure.
* `WuStepDLix.S` looks free and is not, because `hslice` is stated against
  whichever `S` was chosen and `hslice_of_props` proves it only for
  `chernSplitOfGraded`.  `lixChernSplit` is now that choice, named.

**I reported one finding wrong and corrected it within the hour.**  I told the
lead that three endgame inputs were unowned with my name on them, taking
`LemmaTwoStepDLix`'s docstring at its word.  `S` was not one: it was closable in
four lines from parts that had been on origin for hours.  The docstring was
stale and I repeated it instead of checking it.  The rule I already had —
grep before declaring a gap — applies to a PEER'S CLAIM of a gap exactly as it
applies to my own, and a docstring naming an owner is a claim, not a fact.

### TRAP: a name free on origin can be taken before you push

dupscan caught `chernSliceNatural_lixChern` colliding with an untracked peer
file in the shared tree.  I had grepped origin before building and it was free;
cc-cohom-api derived the same theorem from the same message and gave it the same
name.  The pre-build grep cannot see in-flight peer work, which is exactly why
the dupscan gate sits before the push.  Resolution: the name on origin wins and
the in-flight file drops its copy.

## 2026-09-06 — THE INVARIANCE LAYER, AND THE BRIDGE TO V

* `ChernEulerPushforwardSize` (b8c979497, **PROBE GREEN, 8826 jobs**)
* `ChernOfInvariance` (34f43947d, **PROBE GREEN, 9150 jobs**)
* `LIXChernSliceValueBridge` (3f50a8dde, **PROBE GREEN, 9160 jobs**)

The chain, and where the only real content sits:

* `CPn.eulerOfBundle_pushforward_size` / `eulerOfBundle_pushforward_iso` — the
  Euler class does not see the SIZE of the index it is pushed into.
  `ChernEulerIndex` already had independence of the injection and the `iterFin`
  descent, but both fix the target size, and comparing two bundles with different
  index types needs the size free.  The obstruction is arithmetic, not geometric:
  `M + N` and `N + M` are not the same term.  Fixed by giving the common size as
  an EQUATION `a + k = N` and discharging it by `subst`, so a caller instantiates
  it both ways round.
* `LH.tautEulerOf_eq_of_bundleIso` — the generator transports.  This is the only
  step of invariance with content, because `tautEulerOf` reads its `Fin` size off
  the index type.
* `LH.chernOf_eq_of_bundleIso` — invariance, as `chern_map_of_square` with the
  IDENTITY ring map.  Naturality and invariance are the same theorem with a
  different ring map, which is why neither needed a new idea.
* `LH.chernOf_pushforward`, `LH.chernOf_congr` — the two corollaries the endgame
  consumes.
* `LH.chernOf_lixSlice_eq_vBundleY` — the bridge: the classes of the restricted
  mapping torus are the classes of `V`.

Everything is stated at an arbitrary injection and degreewise, so a LINE is the
rank-one case rather than a separate lemma.  cc-steenrod asked for the line-level
statement and I declined to write it separately for exactly that reason; the
second-summand inclusion is one instantiation, not the hypothesis.

### Why the bridge is cheap, and it was nearly not

The two bundles are not isomorphic-up-to-a-unitary-field, they are EQUAL in a
block: `mappingTorus_lixSlice_baseY` says the restriction at the marked points is
`fromBlocks 0 0 0 (VmatY y)`, because the clutching field is annihilated at the
pole.  So the bridge is `chernOf_congr` then `chernOf_pushforward`, and the
differing index sizes are absorbed by the invariance lemma rather than by any
reindexing at the LIX layer.

### TRAP, third occurrence tonight: `ext` recurses past the point of the proof

`ext x` on an equality of `Bundle`s does not stop at `Bundle.ext`; it continues
into the matrix entries and hands back `p x i j = q x i j`, which the pointwise
hypothesis does not close.  Same shape as `ext` on a morphism into a product of
spheres running into `EuclideanSpace` coordinates.  The rule that covers both:
when a target has a chain of `@[ext]` lemmas, name the top one as a TERM rather
than invoking the tactic — `DFunLike.ext _ _ h` here, `ContinuousMap.ext fun _ =>
rfl` there.  `ext x : n` also works but requires guessing the depth.

### TRAP: a parse error manufactures a `sorry`

Omitting `open scoped Matrix` made `ᴴ` a parse error, and Lean then reported
`declaration uses 'sorry'` sixty lines below, in a declaration containing no such
thing.  The banned-token scan on the SOURCE was clean throughout.  Do not chase
the reported `sorry`; fix the first parse error and it goes.

## 2026-09-06 — THE ROOTS, THE GENERATOR, AND cc-thom's LAST INPUT

* `ChernTautRestrict` (7c4fbb066, **GREEN, 9153**) — the tautological class
  restricts along the hyperplane.
* `ChernTautHyperIso` (14adf888f, **GREEN, 9181**) — the same in cc-thom's spelling.
* `ChernLineEulerNatural` (37156d57f, **GREEN, 9153**) — `lineEulerOf` is natural
  and normalised.
* `SliceVLineRoots` (546facd8b, **GREEN, 9162**) — **the roots of `V`.**
* `SliceVGenerator` (199e159b0, **GREEN, 9163**) — the generator, stated once.

`LH.pull_tautEulerOf_of_iso` is the general fact and it subsumes THREE uses: the
base change, the bundle isomorphism, and the hyperplane.  A map of
projectivisations carrying tautological line to tautological line up to
isomorphism carries the class to the class, and the isomorphism may change the
index type.  That last clause is the entire difficulty, and it is paid for once
by `CPn.eulerOfBundle_pushforward_iso`.

`LH.lineEulerOf_vLineYBundle_inr` is the root: the line in block `β` has Euler
class the generator of the `β.1`-th factor, pulled back.  Since `HBlk dd` is
`Σ j, Fin (dd j)`, all `dd j` blocks over one factor carry the SAME class, which
is why the multiplicity is `dd j` copies of one generator rather than `dd j`
unrelated roots.

### The pattern this session settled into

Every one of tonight's five modules is `eulerOfBundle_pushforward_iso` or
`chern_map_of_square` at a different instantiation.  Naturality is the square with
a pullback ring map; invariance is the same square with the IDENTITY ring map; the
hyperplane, the base change and the block inclusion are all one lemma about the
tautological line at unrelated index sizes.  Pre-empting the general form each
time cost one extra lemma and saved four.

### TRAP: `blockDiagonal'_apply_ne` with `_` for the block family

Passing `_` for `M` leaves `o`, `m'` and `n'` as metavariables, and Lean solves
them against the explicit `i j` instead, reporting the block inequality as an
inequality of `Fin` SIZES (`dd b₁.fst + 1 ≠ dd b₂.fst + 1`).  The expected type
never drives it, because the term elaborates bottom-up.  Fix: pin
`(m' := fun b => Fin (dd b.1 + 1))` and `(n' := ...)`; `_` for `M` is then fine.

### TRAP: a dependent Sigma index leaks through `subst`

`by_cases` on two block equalities then `subst` renames unpredictably, since Lean
may eliminate either side of `b₁ = β`.  Deciding BOTH `by_cases` before any
`subst`, and writing `_` for every block argument afterwards, makes the proof
name-agnostic.  Isolating the three `hLine` entry cases into their own lemmas kept
the dependent index out of the main argument entirely, which is what turned three
errors into none.

## 2026-09-06 — LANE STATE: NOTHING OPEN, EVERYTHING WIRED

Thirteen modules landed this session.  All are on origin byte for byte, nothing of
this lane is uncommitted, and all thirteen are **reachable from the root** by a
transitive import walk of `origin/main` (root closure 4801 modules).  That last
check is the one worth repeating: a module can be green, pushed and byte-verified
and still be invisible to the root build.

* `ChernSliceNaturality` (cf1f83b6a, 9148) · `LIXChernSlice` (8c7a0e1e5, 9154)
* `LIXChernSliceNatural` (a501b49a1, 9155) · `LIXChernSplit` (1a6884b8a, 9156)
* `ChernEulerPushforwardSize` (b8c979497, 8826) · `ChernOfInvariance` (34f43947d, 9150)
* `LIXChernSliceValueBridge` (3f50a8dde, 9160) · `ChernTautRestrict` (7c4fbb066, 9153)
* `ChernTautHyperIso` (14adf888f, 9181) · `ChernLineEulerNatural` (37156d57f, 9153)
* `SliceVLineRoots` (546facd8b, 9162) · `SliceVGenerator` (199e159b0, 9163)
* `SliceRootsBlock` (fbe438692, 9181)

### The two theorems this session actually consisted of

`chern_map_of_square` with a pullback ring map is NATURALITY; with the identity
ring map it is INVARIANCE.  `CPn.eulerOfBundle_pushforward_iso` covers the base
change, the bundle isomorphism, the hyperplane and the block inclusion, because
all four change the index type and nothing else.  Every module above is one of
those two at a different instantiation, plus the LIX-side identifications.

### What the fleet adopted from this lane

**Rule 17, strengthened** (lead, 07:49): the producer of a name lands it as a
properties-free definition on origin FIRST, and the consumer states against the
name, never against a description.  This came from cc-steenrod landing `vRoot`
and `baseYFactor` instead of sending them.  It mattered concretely: I had proved
their statement at my own `evalFactor`, which is their `baseYFactor` written
twice, and a description would have handed them a lemma crossing by `exact` and
not by `rw` — discovered inside a rewrite chain rather than at the seam.

### Open, and owned elsewhere

* `hu` / `hclass` — ruled cc-thom's.  This lane's part is by NAME ONLY: if
  `gammaCoeff` and `chernOf` meet definitionally nowhere at the mapping torus,
  cc-thom sends that one identity and this lane proves it.  Do not start unasked.
* `hres`, the Thom-class restriction naturality — accepted from cc-thom under
  rule 13, awaiting their goal as terms.
* Post-endpoint hygiene: retire `LH.lineEulerOf_pushforward` by importing
  cc-steenrod's `CharClass.lineEulerOf_pushforward` (438667a59, landed first).
  Separate commit, AFTER the endpoint is green, never before.
