# ms-cite-2: literature inputs cited in tex 1338–2507

Lane ms-cite-2, wave 2 of session nonsofic-existence-49 (2026-09-13). Manuscript `non_mf_groups_exist.tex` at origin/main
835fa3ee5 (2507 lines). Census rows are from `metadata/NON_MF_SENTENCE_MAP.tsv` at the same tip; the census line numbers
in those rows are at the pre-chain-core hash, so rows were matched by sentence text.

"Proved" below means the carrier is a theorem with `#audit_closed_axioms` on main (standard axioms only, no binder), in a
module reachable from `GroupApproximation.lean`. Every chain below was checked at the declaration level: the endpoint's
type, its audit line and its import path. No claim here rests on a local build.

## Summary

- tex 1338–1540 (sec:chain-core up to thm:core-ring-reflection) contains no citation.
- 17 `\cite` commands in the range name 24 cited items.
- **No formalized row in the range has a cited result assumed in its chain.** Every row that cites a result used as a
  proof step has a proved carrier.
- **Still assumed:** Hull Theorem 7.1 (clauses (a), (c), (e), and clause (d) in the proof paragraph), Hull Corollary 7.4,
  the Fournier-Facio configuration [FFF §2], and "Hull's small cancellation theorem again applies" in the proof of
  lem:saturation. All four enter only through the W1 binder
  `GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement` (hgreendlinger). hbridge is closed at 18682110d,
  KO at f65f99f17 and hW at 47b31bef8. The rows are partial, and the other swarm's W1 lanes plus w1-binder-1..8 own the
  binder.
- The ct block's two citations (EJZ at 1557, GHW at 1798) have proved carriers. Their rows are unassigned pending the ct lanes.

## Ledger

| tex | citation | role | census row (status) | Lean carrier | verdict |
|---|---|---|---|---|---|
| 1557 | EJZ Thm 1.1 | proof step of prop:bilateral-three: `EL_3(S)` has (T) for finitely generated `S` | ct block, unassigned (owner ct-bilateral-mf) | `Manuscript.OneSidedMFRadical.FullDefectRingEJZUnconditional.ejz : FinitelyGeneratedRingGeneralRankElementaryPropertyT` (∀ ring `A`, `IsFinitelyGeneratedRing A` → ∀ `n ≥ 3`, `HasKazhdanPropertyT.{0,0} (elementaryGroup (Fin n) A)`), proof `IntegralColumnPlaneClosure.finitelyGeneratedRingGeneralRankElementaryPropertyT`; `#audit_closed_axioms ejz`; root-imported | proved |
| 1798 | GHW Thm 4 | proof step of the rank-two remark: f.g. subgroups of `GL_2(k[z,z⁻¹])` are Haagerup | ct block, unassigned (owner ct-rank-two-limit) | `GHW.printedGHWTheoremFour : PrintedGHWTheoremFour` (every countable subgroup of `GL_2(K)`, `K` a field in `Type`), GHWTheoremFourClosed, `#audit_closed_axioms`, root-imported; applies through `k[z,z⁻¹] ⊂ k(z)` | proved. The finite-product closure of Haagerup and "(T) + Haagerup ⇒ finite" (`Haagerup.kazhdanHaagerupFinite`) are ordinary steps, not literature |
| 1813 | Brown, discussion before Prop 3.5.1 | historical attribution, not used | 2acc03ce92d4 (attribution) | none needed | honest |
| 2053 | Elek–Szabó Thm 1 | proof step: soficity passes to directed unions and to extensions with amenable quotient | 2c614717a212 (formalized) | `isSofic_of_every_finset_mem_sofic_subgroup` (Sofic/SoficDirectedUnion) and `SoficByAmenablePermanence.manuscriptSoficOfSoficKerOfAmenableQuotient` (∀-header with only the printed hypotheses: surjection, sofic kernel, amenable quotient), both `#audit_axioms` in `Manuscript/NonMF/Audit/Sec4` (root), plus `AmenableTraceTheorem.manuscriptWSoficFromLocallyRFExtension` (`#audit_closed_axioms`) | proved |
| 2085 | BHV Example 1.7.4(i) | proof step: `Γ̄ ≤ GL_4(ℤ)` has (T) | 77028123cdd6 (formalized) | `CommutingLampCollapse.gammaBar_hasKazhdanPropertyT`, `#audit_closed_axioms` in Audit/Sec4 (root) | proved, but along a DIFFERENT ROUTE: it pushes the presented base's certificate (`LiteralBaseP13PropertyTBridge.manuscriptBaseHasKazhdanPropertyT` ← `LiteralP13HodgeCertificate.p13_hasKazhdanPropertyT`) through the affine quotient; the BHV example itself is not formalized. The census should decide whether a citation sentence needs the cited route |
| 2115 | Hull Thm 3.12 | proof step: choose Hull's generating set `A` | a9dd4b90e479 (partial) | `HullCitationSentences.printedHullGeneratingSetLimitSet`, `printedHullTheorem312LimitSet`, `printedHullTheorem312Osin` (`#audit_closed_axioms`), and `HullTheorem312Lemma58.printedHullTheorem312` (all four clauses as a TFAE, `#audit_closed_axioms`); root-imported | proved. REGRADE CANDIDATE: the printed endpoint is closed with no `hhard` premise, but the row still names `TorsionFreeLimitSetNotion.manuscriptSentence_hullGeneratingSetLimitSet`, and the baseline still carries `inlined-statement … premise hhard`. Census action |
| 2117 | Hull Def 1.4 | definition of *suitable* | 615720614d7a (definition) | `Manuscript.NonMF.TorsionFree.Suitable` (both clauses) | honest |
| 2119 | Hull Thm 7.1 (a), (c), (e) | the transition sentence names the source of thm:hull | 0a882030dcd9 (structural); thm:hull rows 8aead549f1fe and 4895f03fdf5f (partial) | `TorsionFreeGreendlingerLeaf.printedHullTheorem_of_greendlinger` | ASSUMED through hgreendlinger (W1) |
| 2131 | Hull, proof of Thm 7.1, clause (d) | proof paragraph (m = 1, induction on m) | bcc99703f838 (partial) | `printedHullProofParagraph_of_greendlinger` | ASSUMED through hgreendlinger (W1) |
| 2146 | Osin Lemma 7.1 | proof step: an infinite normal subgroup acts non-elementarily | c650b0a20b89 (formalized) | `GGT.OsinPrinted.osinLemma71Printed` (GGT/OsinLemma71Printed, `#audit_closed_axioms`, reached through Audit/Sec5 and OsinCitedSentencesClosed); `OsinCitedSentencesClosed.manuscriptSentence_saturationSuitableClosed` (`#audit_closed_axioms`, root) | proved |
| 2147 | Hull Cor 5.7 and Lemma 5.8 | proof step: `N_0 = ⟨h_1, h_2⟩` is suitable | 2d1cd22e5f49 (partial) | `HullCitationSentences.printedHullCorollary57` and `HullTheorem312Lemma58.printedHullLemma58` (both `#audit_closed_axioms`, root) | both cited results proved; the row is partial only for "Hull's small cancellation theorem again applies" (thm:hull, W1) |
| 2165 | FFF §2 | proof step: the configuration `G_0, Γ, t, J` | 8097c371f35d (partial) | `TorsionFreeGreendlingerLeaf.fournierFacioParagraph_of_greendlinger` with `kotowskiOllivier_closed`, `finitelyPresentedInfiniteSimple_closed` and hbridge closed | ASSUMED through hgreendlinger only (W1) |
| 2167 | Hull Cor 7.4 | proof step: `G_0` as a common acylindrically hyperbolic quotient | dab2f2bfe084 (partial) | `HullCorollary74.printedHullCorollary74_of_greendlinger` | ASSUMED through hgreendlinger only. The row note "neither leaf has an unconditional producer yet" is stale, since hbridge closed at 18682110d |
| 2212 | Osin Thm 1.2 | proof step: `Q` contains a non-degenerate hyperbolically embedded subgroup | 92115dd7edef (formalized) | `TorsionFreePrinted.osinTheorem12Printed_unconditional : OsinTheorem12Printed` (Manuscript/NonMF/OsinTheorem12NonDegenerate, `#audit_closed_axioms` in Audit/Sec5, root) via `exists_isNonDegenerate_isHypEmbedded` | proved |
| 2214 | DGO Thm 2.35 | proof step: simplicity and unique trace | f2bf6328169e (formalized) | `TorsionFreePrinted.dgoTheorem235Printed` (DGOTheorem235Proof, `#audit_closed_axioms`, root), from `naiveFreeProductAtAcylindricallyHyperbolic` (`#audit_closed_axioms`) | proved |
| 2216 | Gerasimova–Osin Thm 1.1 | proof step: stable rank one | f2bf6328169e (formalized) | `TorsionFreePrinted.gerasimovaOsinTheorem11Printed` (GerasimovaOsinTheorem11Closed, `#audit_closed_axioms`, root); the sentence endpoint `manuscriptSentence_algebraSimpleUniqueTraceStableRank_closed` takes only the printed hypotheses on `Q` | proved |
| 2226 | OAI | origin story | 5b0dfc92ce36 (provenance) | none needed | honest |
| 2272 | Eckhardt | acknowledgment | c194394e4605 (attribution) | none needed | honest |

## Items for the census lane

1. a9dd4b90e479 (Hull Thm 3.12): the printed endpoint is closed. Consider dropping the stale `hhard` declaration from the
   row and retiring the baseline line `inlined-statement …TorsionFreeLimitSetNotion.manuscriptSentence_hullGeneratingSetLimitSet`,
   then regrading.
2. 77028123cdd6 (BHV Example 1.7.4(i)): the conclusion is proved along a different route. Record the route in the row note.
3. dab2f2bfe084 (Hull Cor 7.4): the note about the two leaves is stale; only hgreendlinger remains.

## Nothing built

Every assumed cited result sits behind hgreendlinger, which the other swarm's W1 lanes and w1-binder-1..8 own, so this lane
built no module.

## Binder 6 help (09-13 ~17:40): `CopyClean.side_cell`

Main's next item for this lane is one leaf of W1 binder 6 (`OsinSectionPocketFaceSetSectionStatement`). Binder 6 still
needs an O-equivalent copy with legal labels that satisfies the six edge conditions `PocketWalk.CopyClean`
(Estimating/OsinPocketCopyWalk). The owners of record are:

| field | owner |
|---|---|
| `spur` | hs-vanishes, landed at 36ff632cd |
| `cell_outer` | w1-binder-6 |
| `side_outer` | w1-binder-6, after this lane's transport interface lands |
| `cell_self`, `regions` | leavitt-units (ruling 14:00, copies (b) and (c)) |
| `side_cell` | this lane (agreed with w1-binder-6 by direct message, 17:39) |

CLAIM inner cell-side thickening:
- `GroupApproximation/GGT/VanKampen/SurgeryCellSideThickening.lean`: the statement, the counting and the induction.
- `GroupApproximation/GGT/VanKampen/SurgeryFaceEdgeDoublingSideRegions.lean`: the regions transport.
- `GroupApproximation/GGT/VanKampen/Estimating/OsinPocketCopySideCell.lean`: the `side_cell` field on the copy.

The statement: a distinguished section family has a distinguished section family over the same cuts, on an
O-equivalent diagram, in which no left or right side dart of a selected region has across it a relator face with at
least two darts that lies in no selected region. The regions correspond with the same weight, target profiles and
source indices.

The route has four parts.
- **Surgery.** `FaceEdgeDoubling.diagram` puts a G digon in the relator face at the dart across the side dart.
- **Transport.** `FaceEdgeDoublingRegions.contiguityGeometry` needs the face across the doubled dart to lie in no
  region, which fails for the region owning the side dart. The new transport replaces that hypothesis with: the
  doubled dart lies in no source or target arc. This follows from the boundary cycle having no duplicate and from the
  selected regions being disjoint.
- **Induction.** Induct on the number of such darts, as in `SurgeryOuterSpurThickening.exists_spurFree`.
- **Monogon source cells.** They need no copy: the one dart lies in the source arc of a nondegenerate exterior region.

### Landed (09-13 ~18:20)

All four modules are probe GREEN (0913-175740-65393 statement, 0913-180914-12240 transport and model,
0913-181548-50528 proof and field), with a BUILT line per module. They are queued for wiring.

| sha | module | declarations |
|---|---|---|
| 3ac666f81, dc394dd8e | `GGT/VanKampen/SurgeryCellSideThickening` | `CellSideThickening.IsCellSideDart`, `cellSideCount`, `CellSideThickeningStatement`, `cellSideThickening : CellSideThickeningStatement` (`#audit_closed_axioms`), `exists_cellSideFree`, `exists_cellSideFree_of_invariant`, `sectionFamilyOfArcs`, `cellSideCount_lt`, `exists_of_isCellSideDart` |
| bb3a56f4e | `GGT/VanKampen/SurgeryFaceEdgeDoublingSideRegions` | `FaceEdgeDoubling.contiguityGeometryOfArcs`, `ArcAvoiding`, `FamilyArcAvoid`, `familyArcAvoid_of_side`, `dart_not_mem_{source,target}Arc_of_{side,not_mem_cycle}`, `regionFamilyOfArcs` with `_card`, `_weight`, `_pairwise`, `_profile`, `_noLoop`, `regionFamilyOfArcsEquiv` with `_profile`, `_source` |
| bb3a56f4e | `GGT/VanKampen/SurgeryCellSideThickeningModel` | `decide` model of one doubling: one cell-side dart before and none after, every old dart keeps its reverse, the region keeps its boundary darts |
| dc394dd8e | `GGT/VanKampen/Estimating/OsinPocketCopySideCell` | `CellSideThickening.side_cell_of_noCellSideDart`: on a least-area copy with no cell-side dart, the field `side_cell` for two distinct exterior regions of one cell |

The model test found no false printed identity and no degenerate case.

### Residual for binder 6

Composition order agreed with w1-binder-6 (18:1x): outer thickening, then cell-side thickening, then `cell_self`.
- The cell-side stage must keep the outer conditions. `exists_cellSideFree_of_invariant` carries any invariant preserved
  by one doubling step.
- The module `GGT/VanKampen/SurgeryCellSideThickeningPreserves.lean` is drafted: `faceOf_eq_outer_iff`, the step
  lemmas `noOuterSpur_of_step`, `noOuterCellDart_of_step`, `noOuterSideDart_of_step` and `relatorValues_of_step`, and
  `CellSideThickeningPreservingStatement`.
- It lands once w1-binder-6's `OuterSideThickening` is on main.
