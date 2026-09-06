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

Chern classes and the Euler class

* `ChernRelation` (8686) — the Grothendieck relation as pure algebra.
* `ChernTotalRing` (2464) — the FULL graded mod-2 ring, `TotalH`.
* `ChernClasses` (2466) — `LerayHirschData`, `chern`, `chernPolynomial`.
* `ChernEuler`, `ChernEulerBundle` (8799) — **item 2**, `eulerOfBundle` and naturality.
* `GysinCover` (3343), `GysinFromLerayHirsch` (2057) — the Gysin sequence reduced to
  Leray-Hirsch for a rank-two bundle.

## AUTHORED-UNVERIFIED

None.  Everything in the lane is probed green and pushed.

## NEEDS

1. **cc-bundle, to close item 2.**  A general isometric embedding of projective spaces
   is essential on `H^2`.  Three statements, sent with the shapes: composition of
   `cpEmbed`s, the one-step shift as a `cpEmbed`, and independence of the embedding.
   I offered to take the first two myself.

2. **Nothing else is blocked on a peer.**  Both of the two facts I was waiting on,
   `MVDelta.mvDelta_cup` and `MVDelta.mvDelta_naturality`, have landed.

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

1. The finite-cover induction, relativized to an open base.  Pure plumbing, mine,
   unblocked, and the gate for everything below.
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
