# Lane ms-inverses-2: tex 809–929 (lem:two-copies, lem:rank-two, lem:ring-compression-cell, eq:intertwine)

Lead: session nonsofic-existence-49 (wave 2). Manuscript at origin/main 15ab3ebe5. The census rows are keyed at the
pre-chain-core hash, so census line = tex line − 11 in this range. The comment lines at tex 927–929 are not sentences.

## CLAIM

- CLAIM G1 G2 G3 GroupApproximation/Manuscript/NonMFSentences/OneSidedInversesPrintedSteps.lean
  (ownership check 09-13 ~17:10: no declaration, file or in-flight draft on origin or in the shared tree; the only
  `.files` hit is audit-sec3's RingCompressionCellGeneral, last landed 04:28).

## Verification (37 census rows in range)

Checks run on every carrier: the declaration exists on origin/main; its module is reachable from `GroupApproximation.lean`
(OneSidedCompressor, OneSidedCompressorDefect, RankDescentEmbedding (which imports ProperlyInfiniteUnit and
RankTwoNormalGeneration), RankTwoPrintedSteps, RingCompressionCellGeneral and FullDefectRingSentences are direct root
imports; RankDescentPrintedLemmas and RankFourCompressionCellPrinted come in through OneSidedSentences); endpoints carry
`#audit_closed_axioms`; `Audit/Sec3.lean` audits every named declaration; the statement is at printed generality (every
unital ring; `R : Type` is the repo convention) along the printed route. No literature input: these are ring and
elementary-matrix computations with no cited theorem.

### lem:two-copies (tex 809–829)

| key | sentence | verdict |
|---|---|---|
| d269b2fd7294 | statement hypothesis `ts=1`, `R(1-st)R=R` | PASS: `PrintedTwoCopiesLemma` spells fullness as a finite sum `∑ a_k(1-st)b_k = 1` (the two-sided ideal is `R` iff 1 lies in it) |
| e123b14ddeee | `there are v₀,v₁,w₀,w₁ with w_iv_j=δ_ij` | PASS (forward direction; `∃ s t, …` → `∃ v w` is equivalent to the printed ∀) |
| c90393ba6292 | `Conversely, such elements satisfy w₀v₀=1 and w₁(1-v₀w₀)v₁=1` | **GAP**: the carrier's converse is `∃ s t, ts=1 ∧ 1-st full`, not the two printed identities for the given elements. Fix G1 |
| 9dbe7e587681 | `Put e=1-st, so that es=te=0, and choose a_j,b_j … with ∑a_jeb_j=1` | PASS in content; the row names only the def `RankDescent.ofFull`. Correction: add `OneSidedSentences.manuscriptSentence_twoCopiesSetup` |
| 5870021d2e03 | display `v₀=s^m, w₀=t^m, v₁=∑s^jeb_j, w₁=∑a_jet^j` | PASS; correction: add `manuscriptSentence_twoCopiesDefine` (the four fields, by `rfl`) |
| 91d76a509a2b | `e t^i s^j e = δ_ij e` and the middle-factor reasons | PASS: `e_mul_t_pow_mul_s_pow_mul_e` follows the printed route (`t_pow_mul_s_pow_of_le`/`_of_ge`, `e_mul_s_pow`, `t_pow_mul_e`). Correction: name those four |
| f437c7807b77 | `w₀v₀=t^ms^m=1, w₁v₁=∑a_jeb_j=1, w₀v₁=∑t^{m-j}eb_j=0, w₁v₀=∑a_jes^{m-j}=0` | **GAP**: the carriers state only the endpoints; none of the printed middle sums is carried. Fix G2 |
| 0bbf89803d26 | `Conversely, w₁(1-v₀w₀)v₁ = w₁v₁-(w₁v₀)(w₀v₁) = 1` | PASS in content; the carrier states only `=1` over the bundled structure. Correction: add `manuscriptSentence_twoCopiesConverse` (bare data, both equalities) |

### lem:rank-two (tex 831–865)

| key | sentence | verdict |
|---|---|---|
| 29f5f8b37797, a7e56a7fbc34, 9aa5019b614f | the statement | PASS: `PrintedRankTwoNormalGeneration`; `gen v b = ⁅upperRoot v, lowerRoot b⁆` by `rfl`, Mathlib's commutator `ghg⁻¹h⁻¹` matches the printed product |
| dbdec0d73e03 | rows of `e₁₂(v)e₂₁(b)e₁₂(-v)`, then `D=diag(1+vb,1)` | PASS |
| 053b6de1fe6b | `Let N be the normal closure of D` | PASS (definition `printedN`) |
| 717152bfc217 | `[D,e₁₂(ar)]=e₁₂(vr)`, so `e₁₂(vR)≤N` | PASS |
| 828a8cc4992b | `f=1-vw`, idempotent, `fv=0=wf` | PASS |
| bd35898b630c | `r=vwr+fr`; reduction to `e₁₂(fR)` | PASS |
| 69843250783b | display `z=vf+fw+1-f-vfw` (the splitter drops the display); `zf=vf` | PASS; correction: add `RankDescent.zElt`, `RankDescent.zElt_eq` for the display |
| 5e2b45529464 | `x=vf, y=fw, q=vfw, c=1-f-q`, `z=x+y+c` | PASS |
| a9865697e6f3 | the multiplication table, `z²=q+f+c=1`, `zf=xf+yf+cf=vf` | PASS (every clause and both chains) |
| c97ce3c374b2 | the six-transvection factorization | PASS at the proof's `z` (`z²=1`, so `z⁻¹=z`) |
| db1722e32d5d | `h=diag(z,z)∈EL₂(R)`, `he₁₂(fr)h⁻¹=e₁₂(zfrz)=e₁₂(vfrz)∈N` | PASS in content; correction: add `RankTwoPrintedSteps.manuscriptSentence_rankTwoConjugationIntoN` for `…∈N` |
| 05233e222ae6 | `e₁₂(r)∈N`, then `e₂₁(R)≤N` | PASS |

### lem:ring-compression-cell and eq:intertwine (tex 867–925)

| key | sentence | verdict |
|---|---|---|
| 49be74c2726c | `Let R … ts=1, e=1-st` | PASS |
| 1eb8329e0e6b | `In G=EL₄(R) let L=EL₃(R) occupy coordinates 1,2,3` | PASS; correction: add `OneSidedCompressor.coreEmbedding_range` (`core R` is the image of `EL₃(R)`) |
| 8f9f00fd2f55 | `there are u,c with uLu⁻¹≤L, c∈C_G(L)` and the two identities | PASS (`printedEll = e₂₃(1)`, `printedDefectRoot = e₁₃(e)`) |
| f417d06b695f | off-diagonal entries of `uLu⁻¹` are `sat` | PASS: closure induction over all of `uLu⁻¹`, not only generators |
| fa78bbc31649 | `e²=e`, `es=te=0` | PASS |
| 718cc7b04afd | `u_i = e_{4i}(t-1)e_{i4}(1)e_{4i}(s-1)e_{i4}(-t)` | PASS (RingCompressionCellGeneral, every ring) |
| f52624ced12a | block `(s e;0 t)`, `u=u₃u₂u₁` is the displayed matrix | PASS |
| c0383f82a141 | invertible as a product of elementary matrices | PASS |
| 8ed7601a0e35 | `For 1≤i≠j≤3 and a∈R`, display `u e_ij(a) = e_ij(sat) u` | PASS; correction: add `OneSidedCompressor.compressor_mul_coreRoot`, which is the display itself (the row names only the conjugation form) |
| 8782d1207725 | the entry computation `sa·ts=sa`, `sa·te·t^{j-1}=0` | PASS (every ring) |
| 3e97a39311f3 | `So uLu⁻¹≤L, and eq:intertwine gives the last assertion` | PASS |
| d1142160bf17 | `c=[e₄₁(e),e₁₄(t)]=diag(1,1,1,1+et)` | PASS |
| 83ed5eb3b38c | `c∈C_G(L)` along the diagonal-shape route | PASS |
| 0f4f9e94cc50 | `Both uc and e₁₂(e)u equal u+etE₁₄: last column (e,et,et²,t³)ᵀ(1+et) …; e₁₂(e)u adds e times row 2 …` | **GAP**: `compressor_mul_centralMark` proves `uc = e₁₂(e)u` by a single `fin_cases` computation; neither the common value `u+etE₁₄` nor the two printed column and row reasons is carried. Fix G3 |
| 419d553a0d48 | `So ucu⁻¹=e₁₂(e)`, and the Steinberg relation gives the second identity | PASS; correction: add the Steinberg relation `elementaryRoot_commutator` used by `defect_eq` |

## Builds

All three are LANDED at a74a166ae in `GroupApproximation/Manuscript/NonMFSentences/OneSidedInversesPrintedSteps.lean`
(probe 0913-171514-15612 GREEN, BUILT, md5 of the landed bytes = green record). The module is unwired and queued in
`$NM/wire-queue.txt`. Each endpoint carries `#audit_closed_axioms`; the helper lemmas carry `#audit_axioms`.

- G1 `printedTwoCopiesConverse : PrintedTwoCopiesConverse`: for every ring and every `v, w : Fin 2 → R` with
  `w_iv_j = δ_ij`, `w₀v₀ = 1` and `w₁(1-v₀w₀)v₁ = 1`, along `w₁v₁ - (w₁v₀)(w₀v₁)`. Row `c90393ba6292`.
- G2 `printedTwoCopiesFourEquations : PrintedTwoCopiesFourEquations`: the four printed equations with their printed middle
  sums (`w1_mul_v1_eq_sum`, `w0_mul_v1_eq_sum`, `sum_t_pow_sub_mul_e_eq_zero`, `w1_mul_v0_eq_sum`,
  `sum_e_mul_s_pow_sub_eq_zero`). Row `f437c7807b77`.
- G3 `printedCompressorMarkProducts : PrintedCompressorMarkProducts`: `uc = u + etE₁₄`, `e₁₂(e)u = u + etE₁₄`, the last
  column of `uc` is the last column of `u` times `1+et`, and the first row of `e₁₂(e)u` is row 1 plus `e` times row 2.
  Row `0f4f9e94cc50`.

## Census rows

`metadata/nm-census-rows/ms-inverses-2.tsv`: 9 corrections naming existing on-main carriers (50b95d51d) and 3 rows for the
new carriers (after a74a166ae).

## Range status

Every sentence of tex 809–929 has a carrier at printed generality along the printed route, and no carrier has a literature
binder. The three new rows are `formalized` once the module is wired into the root.

## Item 2 (main, 09-13 ~17:40): help W1 binder 7, `PocketPinchLabelledStatement`

Agreed with w1-binder-7 (17:45). Its holdings: the `0 < ε` repair, the ResidualsPos assemblies, the ε ≥ 1 truth audit,
`OsinPocketFullArc` and a trims module. ms-intro-4 holds "first-turn order survives the edge doublings" (T1, T1'). hull-respell
holds the (b) step (`OsinPocketPinchFirstTurn`, unlanded: `FirstTurns`, `GoodCorners`, `pocketPinchGoodCornerStep`).

Ownership check 09-13 ~17:50: no declaration or file on origin or in the shared tree for either leaf, no in-flight owner in
`lanes/*.files`.

- CLAIM (A) GroupApproximation/GGT/VanKampen/Estimating/OsinPocketWrapRoseFirstTurn.lean: formal model tests of turn condition
  (b) on the wrap rose. `wrapK`'s complement spelling `[3,1]` has neither first turn (audit-sec3's by-hand row), and for every
  ε ≥ 1 the simple rescue `rescueK` (complement spelling `[4]`) is in first-turn order.
- CLAIM (T2) GroupApproximation/GGT/VanKampen/Estimating/OsinPocketOuterSpurFirstTurns.lean: first-turn order survives the
  outer spur thickening (`PocketFaceSet.outerSpurThickening`, kh-cckw de79601b1), stated over the landed `FirstTurn` chain in
  the shape of hull-respell's `FirstTurns`.

### (A) LANDED b122008b7 (probe 0913-175635-59318 GREEN, BUILT, first try)

`Estimating/OsinPocketWrapRoseFirstTurn`, unwired, queued for wiring; no census row (certifies no printed sentence).
- `wrap_complement`: the complement spelling of `wrapK` is `[3,1]`.
- `wrap_not_firstTurn_three_one`, `wrap_not_firstTurn_one_three`, `wrap_not_firstTurnWalk`: `[3,1]` fails the chain and the
  closing turn. This is audit-sec3's by-hand row, now formal.
- `rescue_complement`, `rescue_firstTurn`: `rescueK` has complement spelling `[4]`, closed by a first turn with `k = 5`.
- `wrapRoseFirstTurnModel : WrapRoseFirstTurnModel` (`#audit_closed_axioms`).
- Consequence: the `ε = 0` refutation does not reach the pinch restricted to first-turn order, and at every `ε ≥ 1` the rose
  has a simple witness in first-turn order.

### (T2) LANDED d85fcd6ab (probe 0913-180253-88110 GREEN, BUILT, first try)

`Estimating/OsinPocketOuterSpurFirstTurns`, unwired, queued for wiring after `OsinPocketEdgeDoublingFirstTurns`; no census row
(certifies no printed sentence).
- `PocketFaceSet.outerSpurThickening_firstTurnChain` (`#audit_axioms`) and the closed
  `pocketOuterSpurFirstTurnChain : PocketOuterSpurFirstTurnChainStatement` (`#audit_closed_axioms`).
- It is a corollary of ms-intro-4's `EdgeInsertion.firstTurnChain_map_embed` (c2927f84f) at the outer face, with distinct
  corners from `EdgeInsertion.corners_ne` at index 1, because the thickened map is `FaceEdgeDoubling.map X X.outerFace j hlen`.
  No transport lemma is duplicated.
- With ms-intro-4's T1 and T1', all three corner surgeries (doubling outside K, doubling inside K, thickening at the exterior)
  keep first-turn order, in the same inline spelling of hull-respell's `FirstTurns`.

### Item 2 status

Both claimed leaves are landed. Nothing open in this lane's binder-7 share.

## Item 3 (main, 09-13 ~18:15): help W1 binder 4, `OsinTwoGonHoldsSectionStatement` (C6′), leaf L1

Split proposed to w1-binder-4 in one message (18:20), no collision reported.
- ms-torsionfree holds the inner-following builder (L2 inner, L3).
- w1-binder-4 holds the assemblies (either-follows, copy route), L2 outer, L4/L5.
- The `CopyClean` clause producers belong to w1-binder-6 (spur, cell_outer, side_outer), ms-binary (cell_self), ms-cite-2
  (side_cell) and w1-binder-5 (cell-pocket clauses).

Ownership check 09-13 ~18:25: no rotation lemma for `IsNoncrossingClosedWalk` and no producer of the `regions` clause of
`PocketWalk.CopyClean`, on origin, in the shared tree or in `lanes/*.files`. baseline-debt's landed
`PocketWalk.isNoncrossingClosedWalk_of_copyClean` gives L1 for `K.walk` from `CopyClean`; w1-binder-4's spelling
`source.reverseDarts ++ a.rightSide ++ target.darts ++ b.leftSide` is a rotation of `K.walk`.

- CLAIM L1a GroupApproximation/GGT/VanKampen/Estimating/OsinAppendixEulerTwoGonCopyCleanWalk.lean:
  `IsNoncrossingClosedWalk.rotate` and `append_comm`, and the decomposition walk of two ordered exterior regions is
  noncrossing at least area under the edge conditions, with the arc bounds of `TwoGonEitherFollowsPocketInput`.
- L1b CLAIM WITHDRAWN (09-13 ~18:35): the `regions` clause is ms-intro-2's (`SurgeryRegionPairThickening` and its `decide`
  model, unlanded at 18:21; agreed with w1-binder-5 and listed in w1-binder-6's clause table). This lane builds nothing there and
  consumes `regionPairThickening` when it lands.

### L1a LANDED 2562633bc (probe 0913-182519-25130 GREEN, BUILT, first try)

`Estimating/OsinAppendixEulerTwoGonCopyCleanWalk`, unwired, queued for wiring; no census row (certifies no printed sentence).
- `IsNoncrossingClosedWalk.vertexOf_alpha_eq_next`, `of_next`, `walkKeep_rotate_iff`, `rotate` and `append_comm`: a cyclic
  permutation of a noncrossing closed walk is a noncrossing closed walk.
- `PocketWalk.CopyCleanAt X i x y`: the edge conditions with the source cell given by its index, so a producer need not name the
  pocket walk. `copyClean_of_copyCleanAt` gives `K.CopyClean x y` for every pocket walk `K` from `i`.
- `PocketWalk.exists_noncrossing_decomposition_of_copyCleanAt`: for exterior regions `a ≠ b` of the cell `i` to section `j`,
  target arc of `a` first, least area and `CopyCleanAt S.diagram i a b`, there are a source arc and a target arc with
  `source.reverseDarts ++ a.rightSide ++ target.darts ++ b.leftSide` noncrossing and the four arc bounds of
  `TwoGonEitherFollowsPocketInput`.
- Route: `PocketWalk.exists_of_le`, baseline-debt's `isNoncrossingClosedWalk_of_copyClean`, then `append_comm`.
- Residual of L1: `CopyCleanAt` on the copy, whose six clauses are produced by w1-binder-6, ms-binary, ms-cite-2 and ms-intro-2.
  The following clause (L2) and the subset and avoidance clauses (L4/L5) are other lanes' leaves.

### Item 3 status

L1a landed; L1b withdrawn. Nothing open in this lane's binder-4 share.

## Item 4 (main, 09-13 ~18:40): binder 5 residual (3), a relator cell on the side of a noncrossing cell pocket walk

The hypothesis `hkept` of ms-intro-4's `CellPocketWalk.exists_cellPocketFaceSet_closedWalk_of_orient` (a0ef02fff). ms-intro-2's
`exists_kept_of_cellPocketRegion_of_value` / `_of_leastArea` (step 5) gives a kept cell for pocket regions whose inner cycle is the
walk.

Ownership check 09-13 ~18:45: no walk-level cell kept cell on origin, in the shared tree or in lane reports.

- CLAIM GroupApproximation/GGT/VanKampen/Estimating/OsinPocketCellKeptCellNoncrossing.lean: for a noncrossing cell pocket walk with
  the exterior face off its side and its outer or its inner cycle following, a relator cell on its side. Pocket region from
  `PocketRegion.ofNoncrossingClosedWalk` (outer, with `reclosed_euler`) or ms-torsionfree's `ofNoncrossingClosedWalkInner` (inner),
  then step 5. Model: dgo-analytic's lake map, where only the inner branch fires.
- LANDED 96c1448c3 (probe 0913-183452-73027 GREEN, BUILT, first try), unwired, queued for wiring:
  - `PocketRegion.exists_of_noncrossing_of_eitherFollows`;
  - `GloballyDistinguishedSectionFamily.exists_kept_of_noncrossingCellWalk_of_value` and `_of_leastArea`;
  - the closed `cellPocketKeptCellNoncrossing : CellPocketKeptCellNoncrossingStatement`;
  - the model `OsinPocketCellKeptCellNoncrossing.multipleEdgeLakeInnerBranch`.
- Main 18:40: the exact target is ms-cite-1's `CellPocketWalkSideRelatorCellStatement` (eb678c70a, `OsinPocketMultipleEdgeCopy`),
  consumed by `relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV2Copy`.
  - Its data gives a noncrossing walk (`CellPocketWalkColour.walk_orient`, `isNoncrossingClosedWalk_of_orient`).
  - The exterior face off the side is `CellPocketWalkOuterOffSideStatement` (w1-binder-3, per main).
  - No following clause is in the data, and no producer exists on main; the lake model shows the disjunction is needed.
- CLAIM GroupApproximation/GGT/VanKampen/Estimating/OsinPocketCellSideRelatorCell.lean:
  - `CellPocketWalkEitherFollowsStatement` (new named residual, same data: the outer or the inner cycle of the noncrossing walk
    follows);
  - `cellPocketWalkSideRelatorCell_of_eitherFollows : CellPocketWalkOuterOffSideStatement → CellPocketWalkEitherFollowsStatement →
    CellPocketWalkSideRelatorCellStatement`.
- LANDED 384e67136 (probe 0913-185241-49157 GREEN, BUILT, first try), unwired, queued after `OsinPocketCellKeptCellNoncrossing`
  and `OsinPocketMultipleEdgeCopy`:
  - `CellPocketWalkEitherFollowsStatement`: with the clean walk data, the outer or the inner cycle of the noncrossing walk follows
    its boundary (new named residual, no owner yet).
  - `cellPocketWalkSideRelatorCell_of_eitherFollows`: orientation (`walk_orient`, `isNoncrossingClosedWalk_of_orient`),
    `leastArea_of_oEquivalent S.equiv`, the outer-off-side residual and the either-follows residual, then
    `exists_kept_of_noncrossingCellWalk_of_leastArea`.
- Residuals of `CellPocketWalkSideRelatorCellStatement`: `CellPocketWalkOuterOffSideStatement` (w1-binder-3, per main) and
  `CellPocketWalkEitherFollowsStatement` (unowned). A configuration where neither boundary cycle follows would need a builder that
  does not use following; none is known on main.

### Item 4 status

Kept cell and wrapper landed. Nothing open in this lane's binder-5 share beyond naming the either-follows residual.

## Item 5 (main, 09-13 ~19:05): prove `CellPocketWalkEitherFollowsStatement`, respelled for ms-cite-1's chosen order

Tools named by main:
- w1-binder-4's `BoundaryCycleFaceClass` (a19fd73b8) and its either-follows machinery (c5f2b7378, 704b70f2c);
- ms-torsionfree's inner builder (2d0b61555);
- hull-select's `firstTurnWalkPocketInputs`.
The respelling waits for ms-cite-1's order-choice names.

Model test first. The on-main calibrations disagree on which clause holds:
- lake map (dgo-analytic): the inner cycle follows, the outer does not;
- pinched two-gon (dgo-geometric): the outer cycle follows, the inner does not.

By hand, a walk that touches both ways kills both clauses: an 8-dart planar map, walk `[0,2,4,6]`, with a monogon on the inner side
across dart `0` and a monogon on the outer side across dart `4`. So the disjunction is not a map-level principle, and a proof must
use the family data or the chosen order.

- CLAIM GroupApproximation/GGT/VanKampen/Estimating/OsinPocketCellWalkFollowsModel.lean: the two calibrations and the double-touch map
  where neither boundary cycle of a noncrossing walk follows. Map level only; whether it arises as a cell pocket walk of two optimal
  regions is not decided here.
- LANDED 0f270c624 (probe 0913-191819-69537 GREEN, BUILT, first try), unwired, queued for wiring:
  - `calibration_opposite_clauses`: on the lake map only the inner cycle follows; on the pinched two-gon only the outer cycle
    follows.
  - The double-touch map `M`: darts `0..7`, rotations `(1 0 7 2)` at `A` and `(3 4 5 6)` at `B`, faces `{0}`, `[2,4,6]`, `{5}`,
    `[1,7,3]`, planar.
    - `isNoncrossingClosedWalk_walk`: `[0,2,4,6]` is noncrossing.
    - `walk_innerCycle_not_followsBoundary`, `walk_outerCycle_not_followsBoundary`: `not_followsBoundary_of_monogon` at `0` inside
      and at `5` outside.
  - `doubleTouchNeitherFollows : DoubleTouchNeitherFollows`, audited closed.
- Consequence: `CellPocketWalkEitherFollowsStatement` is not a principle of noncrossing walks. A proof has to use the regions, the edge
  conditions or least area, for example that a monogon on either side of a walk dart cannot be a region face or a pocket face at least
  area. Not attempted before main rules.
- Order: ms-cite-1 respelled the side-relator target as `CellPocketWalkSideRelatorCellBothOrdersStatement` (per-order
  `SideRelatorCellForOrder`). `cellPocketKeptCellNoncrossing` is order-generic, so each order needs its own outer-off-side and
  either-follows inputs. Reply sent to ms-cite-1.

## Item 6 (main, 09-13 ~19:40): the Euler residual, per order, and the generic non-interleaving Euler lemma

Main's ruling: following is the wrong residual (0f270c624, and w1-binder-1's 8c6883be3). w1-binder-6's
`PocketRegion.ofNoncrossingClosedWalkEuler` (2c1a841e8) builds the pocket region from the two reclosing Euler equalities.

Ownership check 09-13 ~19:45: no `CellPocketWalkEulerStatement`, and no non-interleaving Euler lemma, on origin or in the shared tree.
hull-euler has no in-flight Euler file.

- CLAIM GroupApproximation/GGT/VanKampen/Estimating/OsinPocketCellSideRelatorCellEuler.lean:
  - `CellPocketWalkEulerStatement` per order (both reclosings of the noncrossing cell walk keep χ);
  - the side relator cell per order, `SideRelatorCellForOrder`, from the exterior off the side in that order and the Euler
    equalities, through `ofNoncrossingClosedWalkEuler` and step 5.
  - The builder needs the exterior face off the side, so each order uses its own outer-off-side input.
- CLAIM GroupApproximation/GGT/VanKampen/NoncrossingClosedWalkEulerNoninterleaving.lean: for a noncrossing closed walk whose passages do
  not interleave, both reclosings keep χ.
  - This is `vertexCount_add` without `hout`; `edgeCount_add` and `faceCount_add` already need no following cycle.
  - It discharges w1-binder-6's `SectionPocketWalkEulerStatement` and the cell version.
  - Model test first: the double-touch map (non-interleaving, both χ = 2 expected) and the three-petal rose of
    `NoncrossingClosedWalkEuler` (interleaving, torus).
- LANDED eb8811c3c (probe 0913-194438-39906 GREEN, BUILT, first try), unwired, queued for wiring:
  - `CellPocketEulerForOrder`;
  - `CellPocketWalkEulerStatement`;
  - `sideRelatorCellForOrder_of_euler` and `_of_eulerStatement`.
  - ms-cite-1 removed the over-strong both-orders statement (da5b1466e). Its order assembly `copyRegion_of_offSideWalk` still takes
    EitherFollows; asked to respell it to `CellPocketWalkEulerStatement`, with the one-line kept cell through
    `ofNoncrossingClosedWalkEuler`.
- Generic lemma, staged:
  - Stage 1 (writing now): `RotationBetween`, `PassagesNoninterleaving`, and `eulers_of_vertexCount_le`, which gives both Euler
    equalities from `V + |w| ≤ V_in + V_out` by `edgeCount_add`, `faceCount_add`, `reclosedMap_connected` and
    `eulerCharacteristic_le_two`. Named residual `NoninterleavingVertexCountStatement`.
  - Stage 1b: formal calibrations. The rose interleaves; the double-touch and lake passages do not. Hand counts so far: w1-binder-1's
    mixed-touch map has χ = 2 on both sides; the double-touch map needs 3 + 3 vertices, which equals V + |w|.
  - Stage 2: the per-vertex count. At a vertex, k non-crossing chords `(α e, next e)` cut the rotation into k + 1 sectors, shared
    between the two reclosings. Summed over vertices this gives `V_in + V_out = V + |w|`.
  - Separately: non-interleaving for the section and cell pocket walks, from the joint structure (sec2-sentences' hand argument).
- 09-13 ~20:03: API outage mid-turn. Stage 1 had probed green before it (0913-195537-82662).
- Stage 1 LANDED a660c5856 after resume (bytes = green record), unwired, queued for wiring: `RotationBetween`,
  `PassagesNoninterleaving` (spelled with `w.next`), `eulers_of_vertexCount_le`, `NoninterleavingVertexCountStatement`,
  `eulers_of_noninterleaving`.
- Agreement with ms-inverses-4 (main 20:15). ms-inverses-4 proves `PassagesNoninterleaving` for the pocket walks (CLAIM 2647cc6ce):
  `NoncrossingClosedWalkSectorNoninterleaving` (`SectorFree`, `passagesNoninterleaving_of_isChain`) and
  `Estimating/OsinPocketWalkNoninterleaving`.
  - This lane keeps the vertex count, the calibrations and the Euler wiring.
  - My planned generic passages lemma is dropped, because ms-inverses-4's chain lemma covers it.
- CLAIM GroupApproximation/GGT/VanKampen/Estimating/OsinPocketWalkEulerNoninterleaving.lean:
  - `SectionPocketWalkNoninterleavingStatement` and `CellPocketWalkNoninterleavingStatement` (the named targets for ms-inverses-4);
  - `sectionPocketWalkEuler_of_noninterleaving`, `cellPocketWalkEuler_of_noninterleaving` and
    `sectionPocketKeptCell_of_noninterleaving`.
- CLAIM GroupApproximation/GGT/VanKampen/NoncrossingClosedWalkEulerNoninterleavingModels.lean: calibrations.
  - The three-petal rose `threeRose` [0,2,4] is noncrossing with interleaving passages.
  - The lake and the double-touch walk have non-interleaving passages, through ms-inverses-4's chain lemma.
- 21:36 LANDED 358515a30 `Estimating/OsinPocketWalkEulerNoninterleaving` (probe 0913-213002-3572 GREEN), unwired, queued.
- 21:42 co-probe 0913-214214-80171 GREEN: `PassagesNoninterleaving` respelled on positions (`w.get i`, `finRotate`), with the Props
  module on top. Landing after the 23:12 resume.

## Item 7 (main, 23:12): absorb ms-inverses-4's non-interleaving leaf

ms-inverses-4 is not resumed. Its claim (2647cc6ce, revised 3c646c697) passes to this lane.
- GroupApproximation/GGT/VanKampen/NoncrossingClosedWalkSectorNoninterleaving.lean, from its unprobed draft (attic 9a60fa751).
  - Rewritten for the positional spelling: `SectorFree`, `PassageSectorFree`, `sectorFree_of_sigma_eq`,
    `not_rotationBetween_of_sectorFree`, `rotationBetween_of_sectorFree_rev`, `get_finRotate_of_isChain_closes`,
    `passagesNoninterleaving_of_forall_get`, `passagesNoninterleaving_of_isChain`, `IsNoncrossingClosedWalk.passagesNoninterleaving`.
  - Dropped the `w.next` helpers and the rotation lemma, which have no consumer.
- CLAIM GroupApproximation/GGT/VanKampen/Estimating/OsinPocketWalkNoninterleavingJoints.lean (ms-inverses-4's planned path, not written):
  - every joint of the section pocket walk and of the cell pocket walk is a region boundary step (free sector) or a face step (free
    stretch back);
  - closed discharges of `SectionPocketWalkNoninterleavingStatement` and `CellPocketWalkNoninterleavingStatement`.
- CLAIM GroupApproximation/GGT/VanKampen/Estimating/OsinPocketCellWalkNoninterleavingJoints.lean: the cell half, split off so a failure
  in one proof does not block the other. The section half stays in `OsinPocketWalkNoninterleavingJoints`.
- 23:2x LANDED 2816ef630: `PassagesNoninterleaving` on positions (probe 0913-214214-80171 GREEN).
- 23:3x LANDED 418b3c026: `NoncrossingClosedWalkSectorNoninterleaving` (probe 0913-232715-30986 GREEN), unwired, queued.
- Calibrations `NoncrossingClosedWalkEulerNoninterleavingModels`: the first probe 0913-231926-98884 was RED.
  - Cause: `decide` saw free `Fin` proofs after `interval_cases`.
  - Fixed with `fin_cases`; re-probing.
- 23:45 re-probe 0913-234547-8879 RED on the linter: two one-case `interval_cases b <;> decide`. Fixed with `obtain rfl : b = 1`.
- 23:5x the joints co-probe did not run: the probe's `git fetch` failed on DNS. From ~23:55 github.com does not resolve and the MSI master
  socket is gone. A watcher lands and probes once both return.

### Stage 2 design (authored during the outage)

The vertex count at a vertex `v` reduces to chord combinatorics.
- Rotation at `v` meets the passage endpoints alternately: after a reversed walk dart `α d` comes an arc of darts internal to the inner
  side, then a walk dart, then an arc internal to the outer side.
  - Reason: `faceOf (σ x) = faceOf (α x)`, and faces change side only across walk edges.
- The inner reclosing's rotation follows `σ`, except that at `α d` it jumps to `next d`. The outer reclosing's rotation follows `σ`,
  except that at a walk dart `e` it jumps to `α (prev e)`. Both preserve the old vertex.
- Label the endpoints `α_1 e_1 … α_k e_k` in rotation order and let the passages match `α_j` with `e_{m(j)}`.
  - Inner orbits at `v` are the cycles of `m ∘ ρ`; outer orbits are the cycles of `m⁻¹`; here `ρ` is `j ↦ j+1`.
  - The count needed is `c(m ∘ ρ) + c(m⁻¹) ≥ k + 1`. It holds with equality exactly when the chords do not cross. The rose `[0,2,4]` has
    k = 3 and a count of 2, which is the torus.

Narrowed residual, enough for both pocket walks:
- `SectorFreeVertexCountStatement`: every passage has a free sector (`PassageSectorFree w[i] w[i+1]`) ⇒ `V + |w| ≤ V_in + V_out`. It
  is weaker than `NoninterleavingVertexCountStatement`, and the joints modules produce its hypothesis directly.
- Under that hypothesis every passage is short (`m(j) = j`) or adjacent (`m(j) = j − 1`). Since `m` is a bijection, all passages at `v`
  are of one kind.
  - All short: 1 inner orbit, and k outer orbits, each {α_j, inner arc, e_j} with one walk dart.
  - All adjacent: k inner orbits, each {e_j, outer arc, α_{j+1}}, and 1 outer orbit.
  - Untouched vertex: one orbit, on the reclosing of the side it does not lie in.
- Lean route: classifiers by first hit of rotation, as in hull-euler's `innerVertexClass`, restricted by vertex kind through
  `CombMap.card_orbit_subtypePerm_add`. At short vertices the inner rotation is the first return of `σ`, and at adjacent vertices the outer
  rotation is (`PermFirstReturn`). The other side is classified by the unique walk dart in each orbit.
- 00:13 network back. Report (6380a985e) and attic copies (e0d824adc, 28b9c2334) landed.
- 00:14 co-probe 0914-001357-68038: the calibrations BUILT, but the section joints module failed. Both fixes are in the tree:
  - `Relation.ReflTransGen.mono` takes a `≤` argument, so the proof now uses induction;
  - `subst` on the projection `x.2.target = none` fails, so a variable-target private lemma is used.
- 00:38 and 00:58: MSI hop died twice (rc=255). A watcher fetches the remote verdict once the master returns.
- Stage 2 files written offline, unprobed:
  - `NoncrossingClosedWalkEulerSectorFree`: `SectorFreeVertexCountStatement` and `eulers_of_sectorFree`;
  - `NoncrossingClosedWalkReclosedVertex`: both reclosed rotations stay at the old vertex;
  - `NoncrossingClosedWalkRotationSides`: sides along the rotation, with endpoints alternating.
- Next piece: the first endpoint after a dart, and the local dichotomy. A passage that is not adjacent is followed at its vertex by a
  passage that is not adjacent.
- 01:28 remote verdict of 0914-005813-45742:
  - `NoncrossingClosedWalkEulerSectorFree` and the section joints module BUILT.
  - The cell joints module failed: `have hlea' := leastArea_of_oEquivalent …` could not infer the implicit `m`. Fixed with a typed `have`.
- 01:35 and later: DNS down again. A watcher lands the attic copies and co-probes seven modules once github and MSI are up: calibrations,
  sector-free residual, both joints, reclosed vertex, rotation sides, passage kinds.
- Written offline: `NoncrossingClosedWalkPassageDichotomy`.
  - `faceOf_sigma_pow_not_mem_of_free`: along a free stretch the darts stay outside the side.
  - `eq_of_adjacent_of_free`: an adjacent passage is the only passage whose free stretch ends at its reversal.
- Remaining plan for the count:
  1. The first reversal of a walk dart at-or-after a dart, and the global dichotomy at a vertex (all passages adjacent or none), by
     induction along the rotation using `eq_of_adjacent_of_free`.
  2. The inner classifier into `{v // ¬AdjKind v, v has a retained inner dart} ⊕ {i // adjacent i}`, and the outer classifier into
     `{v // AdjKind v or untouched outer} ⊕ {i // ¬adjacent i}`. Invariance goes through `vertexOf_innerSigma` / `vertexOf_outerSigma`;
     completeness at one-kind vertices through `PermFirstReturn.sameCycle_iff` on the restricted rotations.
  3. The count `V_in + V_out = V + |w|`, which discharges `SectorFreeVertexCountStatement`, then both pocket Euler residuals through the
     joints modules.
- 09-14 08:19: a laptop reboot wiped /private/tmp, the old $NM with it. Main rebuilt the infra at 08:3x at
  `/private/tmp/…/f907d0cb-17e5-443b-a723-7114e9553db6/scratchpad/nm`. All green records were lost.
  - Overlay re-registered: 19 paths.
  - One co-probe 0914-0835 of the ten unlanded modules: calibrations, sector-free residual, both joints, reclosed vertex, rotation sides,
    passage kinds, passage dichotomy, vertex kind, passage internal.
- Written offline, not yet probed:
  - `NoncrossingClosedWalkVertexKind`:
    - `PassageAdjacent`;
    - `exists_first_alpha_after`: the first endpoint after a walk dart is a reversal;
    - `passageAdjacent_of_vertex`: one adjacent passage makes every passage at its vertex adjacent, by strong induction along the
      rotation.
  - `NoncrossingClosedWalkPassageInternal` (`faceOf_sigma_pow_mem_of_free`, `internal_sideFaces_of_short`) and
    `NoncrossingClosedWalkPassageInternalOuter` (`internal_sideOutside_of_free`): the darts inside a free sector or stretch are internal
    to one side, so each reclosing jumps over them in one first return.
- Next: the classifiers, as small files. The inner classifier sends a retained inner dart to its old vertex when that vertex has no
  adjacent passage, and to the first reversal at-or-after it otherwise. The outer classifier is dual.
- 08:28 probe 0914-082834-18302 RED, on one error in `PassageKinds`: `Equiv.Perm.inv_apply_self` is unknown. Fixed by `subst` and
  induction on the power.
- 08:30 probe 0914-083033-23170 GREEN (18 files recorded compiled).
  - BUILT lines for the new five: `PassageKinds`, `PassageDichotomy`, `VertexKind`, `PassageInternal`, `PassageInternalOuter`.
  - Six modules were only replayed, with no BUILT line: calibrations, sector-free residual, both joints, reclosed vertex, rotation sides.
- LANDED b453ea815 `NoncrossingClosedWalkPassageKinds`.
- 09:00 forced rebuild: the six replayed sources are touched (bytes unchanged), so the job purges their oleans. Co-probed with the new
  `NoncrossingClosedWalkInnerKindClass` (`AdjVertex`, `InnerKindIndex`, `exists_first_adjacent`, `innerKindClass` and its two
  characterizations).
- 09:07 probe 0914-083654-43931 GREEN with real BUILT lines for the six forced modules and `InnerKindClass`. The chain landed eleven
  modules in import order:
  - RotationSides 781817f2a, ReclosedVertex bf480aca6, EulerSectorFree 939892337, calibrations ddbb453df;
  - section joints 376d31c6e, cell joints a1091f0c8;
  - PassageDichotomy 27700f376, VertexKind cf3680a57, PassageInternal fa773142a, PassageInternalOuter 9e83f2257, InnerKindClass 544875938.
- 09:2x probe 0914-0920 (InnerKindInvariant BUILT; InnerKindCount RED on one `omega`, since the short sector needs `0 < a`, from
  `alpha_not_mem`). LANDED c95771958 `NoncrossingClosedWalkInnerKindInvariant` (`innerKindClass_sigma`, `next_get_eq`).
- 09:3x probe GREEN: InnerKindCount and `NoncrossingClosedWalkOuterKindClass` BUILT.
  - LANDED f1897074d `InnerKindCount` (`innerKindVertexEquiv`, `inner_vertexCount_kind`).
  - LANDED 6513e3e30 `OuterKindClass` (`Touched`, `OuterKindIndex`, `exists_first_short`, `outerKindClass` and its characterizations).
- 09:4x probe GREEN, first try: `NoncrossingClosedWalkOuterKindInvariant` (`faceOf_alpha_mem_sideOutside_iff`, `prev_get_finRotate`,
  `outerSigma_pow_val`, `outerKindClass_sigma`) and `NoncrossingClosedWalkOuterKindCount` (`outerSameCycle_of_notShort`,
  `outer_vertexCount_kind`). Both landed.
- Co-probing the closing pair:
  - `NoncrossingClosedWalkSectorFreeVertexCount`: `kinds_of_vertex`, `vertexCount_le_kinds`, `card_passageAdjacent_add`,
    `sectorFreeVertexCount : SectorFreeVertexCountStatement`, `IsNoncrossingClosedWalk.eulers_of_passageSectorFree`.
  - `Estimating/OsinPocketWalkEulerSectorFree`: `sectionPocketWalkEuler : SectionPocketWalkEulerStatement`,
    `cellPocketWalkEuler : CellPocketWalkEulerStatement`, `sectionPocketKeptCell : SectionPocketKeptCellStatement`. These take the joints'
    chain relation (vertex step ∧ `PassageSectorFree`) at each position through `get_finRotate_of_isChain_closes`.
- 09:03 probe 0914-090343-18838 RED on one gate: `#audit_closed_axioms` on `eulers_of_passageSectorFree`, which takes inputs. Now
  `#audit_axioms`. Every proof in the module elaborated.
- 09:06 probe 0914-090604-65604 GREEN, with BUILT lines for both modules and the closed-axiom audits of `sectorFreeVertexCount`,
  `sectionPocketWalkEuler`, `cellPocketWalkEuler` and `sectionPocketKeptCell`.
  - LANDED 68838eeae `NoncrossingClosedWalkSectorFreeVertexCount`.
  - LANDED 0bd28eecc `Estimating/OsinPocketWalkEulerSectorFree`.
  - Both queued for wiring.
- **CLOSED** the section and cell pocket Euler residuals as named Props: `SectionPocketWalkEulerStatement`, `CellPocketWalkEulerStatement`,
  `SectionPocketKeptCellStatement`; also `SectorFreeVertexCountStatement`. The general `NoninterleavingVertexCountStatement` stays open
  and has no pocket consumer.
- Consumers that can now drop the hypothesis (other lanes' modules, unchanged here):
  - `heuler : CellPocketWalkEulerStatement`:
    - `sideRelatorCellForOrder_of_eulerStatement`;
    - `copyRegion_of_offSideWalkEuler`, `multipleEdgePocketRegionCopyInput_of_pinchOrderEuler`,
      `osinMultipleEdgePocketRegionCopySection_of_pinchOrderEuler`;
    - the `…Section` and `…Below` variants in `OsinPocketMultipleEdgeCopyOrderSection` and `OsinPocketMultipleEdgeCopyBelow`;
    - `OsinGreendlingerWaistV4Euler`, `V5` and `TorsionFreeResidualsV4Euler`, `V5`.
  - `heuler : SectionPocketWalkEulerStatement` or `hkept : SectionPocketKeptCellStatement`: `osinSectionPocketFaceSetSection_of_euler`,
    `…_of_keptCell`, `sectionPocketFaceSetInput_of_keptCell`, `…_of_residuals`.

## Item 8 (main, 09-14 ~09:15): V7 leaf 8, `OsinTwoGonDecompositionEulerSectionStatement`

The residual comes from w1-binder-1's `Estimating/OsinAppendixEulerTwoGonSpanOfCopyClean` (9f29a234d, consumed by 7ec4e6fe2).
- Target: `TwoGonDecompositionEulerInput`, the Euler pair of a noncrossing walk
  `source.reverseDarts ++ a.rightSide ++ target.darts ++ b.leftSide` with the gap equation and the target ends.
- Told w1-binder-1 once when claiming the item.
- CLAIM GroupApproximation/GGT/VanKampen/Estimating/OsinAppendixEulerTwoGonDecompositionEuler.lean.
- Route.
  - Build a `PocketWalk` from the given arcs and sides. The span equations give `sourceArc_pos`, `targetArc_pos`, `lo_le` and `le_hi`;
    the region fields give the side bounds.
  - `walk_isChain_closes_of_rel` gives the joint relation (vertex step ∧ `PassageSectorFree`) on `K.walk`.
  - The decomposition walk is `K.walk` with its halves swapped. `closedChain_append_comm` moves the relation, and walk membership does
    not change.
  - `eulers_of_passageSectorFree` gives both equalities. `CopyCleanAt` is not used.
- Probe GREEN on the first try (BUILT). LANDED ac902a9c1 and queued for wiring.
- **CLOSED** `OsinTwoGonDecompositionEulerSectionStatement` (`osinTwoGonDecompositionEulerSection`, closed-axiom audit), and
  `twoGonDecompositionEulerInput` for all parameters.
- Consumers: `osinTwoGonHoldsSection_of_copyCleanEuler`, `osinTwoGonHoldsSection_of_cleanCopyEuler`,
  `relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV7`, `TorsionFreeResidualsV7`.
- Sent ct-rank-two-limit all the closures: two-gon Euler, cell and section pocket Euler, kept cell, sector-free count.

## Progress log

- 09-13 ~17:01: ledger landed (d5d320909).
- 09-13 ~17:09: first probe 0913-170959-92332 RED (`(1 + Matrix.single 0 1 P.e) * compressorMatrix P` needed a type
  ascription before `0 j`); text copies preserved (2b9939b2b, 533caf0a9).
- 09-13 ~17:15: probe 0913-171514-15612 GREEN; 9 row corrections landed (50b95d51d).
- 09-13 ~17:20: module LANDED a74a166ae; 3 rows appended; wire queue line added.
