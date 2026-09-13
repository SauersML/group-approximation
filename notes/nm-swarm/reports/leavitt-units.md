# Lane leavitt-units: `cor:leavitt-mf-quotient` (tex 1297–1323)

Roster: row `7916c8696def` (tex 1307, first sentence of the proof), then an audit of the block
for rows that are not closed, with defects fixed by closed carriers in new modules.

## 1. Target `7916c8696def`: `R ≅ R^d`, so `R ≅ M_d(R)` and `H ≅ GL_d(R)`

Target: `non_mf_groups_exist.tex` line 1307, `\label{cor:leavitt-mf-quotient}`, census row
`7916c8696def` ("The maps x ↦ (t_1x,…,t_dx) and (y_1,…,y_d) ↦ ∑_i s_iy_i are mutually inverse
isomorphisms of right R-modules between R and R^d, so R ≅ M_d(R) and H ≅ GL_d(R).").

### What was missing

The census row was `partial`.  Its carrier
`LeavittMFQuotientSentences.manuscriptSentence_unitsEquivGL` states only the conclusion
`Nonempty (Rˣ ≃* (M_d(R))ˣ)`.  The explicit right-module isomorphism with the printed formulas
existed only at d = 2 and R = L_{F_2}(1,2)
(`UniversalLeavitt.manuscriptSentence_rightModuleSelfSimilarity`,
`Leavitt/BinaryLeavittAllRanksUnits.lean`), and nothing derived `R ≅ M_d(R)` from it.

### What this lane adds

Module `GroupApproximation/Manuscript/NonMFSentences/LeavittMFQuotientUnitsGL.lean`
(namespace `GroupApproximation.LeavittMFQuotientUnitsGL`), at every `d` over every field:

* `rightModuleEquiv : R ≃ₗ[Rᵐᵒᵖ] (Fin d → R)`: the printed maps, with the formulas as
  `rightModuleEquiv_apply` and `rightModuleEquiv_symm_apply` (both `rfl`);
* `endEquiv : R ≃+* Module.End Rᵐᵒᵖ (Fin d → R)`: left multiplication
  (`RingEquiv.moduleEndSelfOp`) conjugated along it (`LinearEquiv.conjRingEquiv`);
  `endEquiv_apply_eq_mulVec` shows that `endEquiv x` is left multiplication by the matrix
  `ringEquivMatrix x = (t_ixs_j)_{ij}`;
* `endMatrixEquiv : End_R(R^d) ≃+* M_d(R)`, with `endMatrixEquiv_apply` (the matrix on the
  standard basis);
* `unitsEquivGLPrinted : Rˣ ≃* Matrix.GeneralLinearGroup (Fin d) R`, which agrees with the
  consumed `LeavittMFQuotientGeneral.unitsEquivGL` (`unitsEquivGLPrinted_val_eq_unitsEquivGL`);
* closed endpoint `PrintedLeavittUnitsRightModuleIso` / `printedLeavittUnitsRightModuleIso`
  over every countable field and every d ≥ 2 (`#audit_closed_axioms` passed in the GREEN
  probe).

No literature input.

## 2. Audit of the proof (09-13): two rows graded `formalized` whose carriers missed clauses

### `f6962254d259` (tex 1307, last sentence of the proof)

> So [H,H] ≤ EL_d(R), while EL_d(R) ≤ [H,H] because every homomorphism from EL_d(R) to an MF
> group is trivial (Theorem thm:full-defect-ring).

Defect: the census carrier `KhanhThanhDiagonal.manuscriptSentence_commutatorInElementaryPrinted`
states only the first clause.  The printed reason, in which homomorphisms leave the subgroup
EL_d(R), appeared nowhere in an endpoint.  `LeavittMFQuotientSentences.manuscriptSentence_bothInclusions`
has only the weaker form, for homomorphisms out of GL_d(R).

Fix: module `GroupApproximation/Manuscript/NonMFSentences/LeavittMFQuotientBothInclusions.lean`
(namespace `GroupApproximation.LeavittMFQuotientBothInclusions`):

* `PrintedLeavittBothInclusions` / `manuscriptSentence_bothInclusionsPrinted`: for every
  countable field k and every d ≥ 2, `[GL_d(R),GL_d(R)] ≤ EL_d(R)`, and every homomorphism
  `f : EL_d(R) →* M` to an MF group is trivial, and `EL_d(R) ≤ [GL_d(R),GL_d(R)]`;
* `elementary_le_commutator_of_trivial`, the printed "because": restrict a homomorphism from
  GL_d(R) to EL_d(R).  The abelianization of the countable group GL_d(R) is countable and
  abelian, hence MF (`LeavittMFQuotientGeneral.mfKernels_le_commutator`).
* The second clause is thm:full-defect-ring at L_k(1,d) and rank d
  (`FullDefectRingEJZUnconditional.manuscriptLeavittAlgebraFullDefectRankTwoAllCharacteristics`).

### `4321530b3fec` (tex 1307, third sentence of the proof)

> Khanh--Thanh show that GL_d(R)=EL_d(R)D_d(k), where D_d(k) is the abelian group of diagonal
> matrices with entries in k^×, which normalizes EL_d(R), and that K_1(R) ≅ k^×/(k^×)^{d−1}
> [KhanhThanh, proof of Theorem 7.2].

Defect: the census carriers are the matrix-entry decomposition
(`printedKhanhThanhDecomposition_everyArity`) and the K_1 formula
(`manuscriptLeavittKOneFormula`).  No endpoint stated that D_d(k) is abelian or that it
normalizes EL_d(R).  Those facts existed only as audited lemmas.

Fix: module `GroupApproximation/Manuscript/NonMFSentences/LeavittMFQuotientDiagonalSentence.lean`
(namespace `GroupApproximation.LeavittMFQuotientDiagonalSentence`):

* `PrintedKhanhThanhSentence` / `manuscriptSentence_khanhThanhPrinted`: for every field k and
  every d ≥ 2, with `D_d(k) = KhanhThanhDiagonal.printedDiagonal k d`:
  * every element of GL_d(R) is `E * D` with E ∈ EL_d(R) and D ∈ D_d(k);
  * D_d(k) is exactly the diagonal matrices with entries in k^×;
  * D_d(k) is abelian;
  * D_d(k) ≤ normalizer of EL_d(R);
  * `K_1(R) ≃* k^× ⧸ (k^×)^{d-1}`.
* `mem_printedDiagonal_iff`: the description of D_d(k) by its entries.

No literature input in either module.

### Rows found adequate

| key | line | status | carrier |
| --- | --- | --- | --- |
| `dcf6fa4be4de` | 1298 | definition | `AryLeavitt.AryLeavittAlgebra`, `genS`, `genT`, endpoint binders |
| `6aef426dfc7a` | 1298 | formalized | `LeavittKOneFormulaSentences.PrintedLeavittMFQuotientFull` |
| `7916c8696def` | 1307 | formalized (this lane, §1) | `LeavittMFQuotientUnitsGL.PrintedLeavittUnitsRightModuleIso` |
| `3c68c15758e8` | 1307 | formalized | `LeavittMFQuotientSentences.manuscriptSentence_theoremIdentifiesRadicalAndQuotient` |
| `4321530b3fec` | 1307 | formalized (+ §2 carrier) | `LeavittMFQuotientDiagonalSentence.PrintedKhanhThanhSentence` |
| `f6962254d259` | 1307 | formalized (+ §2 carrier) | `LeavittMFQuotientBothInclusions.PrintedLeavittBothInclusions` |
| `6d3ca647302e` | 1320 | formalized | `LeavittKOneQuotientEvaluations.PrintedLeavittQuotientTrivialRankTwo`, `PrintedLeavittQuotientCyclicFiniteField` |

Proof of thm:mf-quotient-units (tex 1239–1296, 16 keyed rows: formalized, structural or
attribution).  I checked three things for every carrier.  The declaration exists on
origin/main.  Its module has an audit line for it, either directly or through the combined
`manuscriptSentence_itemA`.  The module is root-reachable: `MFQuotientUnitsItemA` is reached
through the root-imported `MFQuotientUnitsStepOnePrinted`.  No closedness defect was found.
This check did not re-read those statements against the printed sentences word by word.

## Status

* LANDED `4f629158e` (row 7916c8696def, orphan).  Probe `0912-102543-53051` GREEN on base
  `552014bcf`, and the bytes on origin are unchanged since.  root-wire held it out of wave 3
  because no probe record named it.  Re-probed 09-13: probe `0913-040613-59510` PROBE GREEN on
  base `be9ca5170`, target named.  No module was rebuilt: the olean was replayed with a matching
  input hash, and the source md5 equals origin.  Re-queued in `wire-queue.txt` with the green
  record tag.
* LANDED `b3083ac22` (rows f6962254d259 and 4321530b3fec, unverified landing).  Probe
  `0913-014841-85842` GREEN on base `b360f7a94`: BUILT and COMPILED both modules, audits
  passed.  The green landing reported NOTHING TO LAND at `674b1b428`, because the bytes
  already matched origin.  Both modules are queued for wiring.
* Census rows: `$NM/rows/leavitt-units.tsv` → `metadata/nm-census-rows/leavitt-units.tsv`
  (`7916c8696def`, `dcf6fa4be4de`, `4321530b3fec`, `f6962254d259`).
* The map still shows `7916c8696def` as `partial` until the census lane merges the rows file.
* Residual Props in this lane's scope: none.
* Report first landed `92e9f4497`.

## 3. W4 help (09-13): `LemmaFourSixDynamicsStatement`

The lead asked this lane to help hl-lemma46 with `LemmaFourSixDynamicsStatement`
(`QTwoLemmaFourSixStatements`, Hyde–Lodha proof of Lemma 4.6, `\label{FPlem3}`).  I proposed a split:

* f;
* J inside [c, d];
* the covering clause;
* the six s_i.

I claimed the s_i.

hl-lemma46 had already landed the whole statement: `QTwoLemmaFourSixDynamics.lean` at `de535e84c`, which
proves `lemmaFourSixDynamics`.  That landing is unverified while its probe runs.  It takes s_i = t^{i+1}
for one push element t (`exists_upsilon_qTwo_push`, `disjoint_pow_image`).

This lane landed nothing for W4.  An alternative for the s_i is in the lane scratchpad only and was
not landed: six products of two F_6' moves with pairwise disjoint targets.  It is kept in case the
powers route goes red.  The lane has asked the lead for reassignment.

## 4. W2 hbridge (09-13)

The lead reassigned this lane to W2, `HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement`.
hull-bridge's split of clause (b) planned CutOutcome, Cut (M2) and Holds (the producer of
`QuotientPeripheralLetterPullbackStatement`), and debt-conditional takes one of them.  This lane takes
the next unstarted one, and asked hull-bridge for its path.

hull-bridge handed this lane the right-designated case of the cut outcome:
`CutLift.pullbackOutcome_right` in a new module `HullSCLemma51LetterPullbackCutRight`, importing
CutLift (`dfa2dfb11`).  The case is: the arc runs through the unknown letter, no letter of `L` reads
at its coset, and `R[j]` does.  I wrote the full proof from the CutBlocks interface.

Before probing, I found the case already green on origin.  hull-component landed
`CutMove.outcome_right` and the case split `CutMove.outcome` (`HullSCLemma51LetterPullbackCutOutcomeRight`,
`47b7225af`, probe `0913-045018-55444`).  hull-bridge then landed `HullSCLemma51LetterPullbackHolds`
(`18682110d`), which proves `cutLiftOutcome` through `CutLift.toCutMove` and `CutMove.outcome`.

So CutRight was a duplicate, and the lane dropped it: not probed, not registered, not landed.  Nothing
on origin references it.  The unlanded file was removed from the tree and kept in the lane backup
folder.  hull-bridge was told.

Nothing landed for W2 by this lane.  The lane has asked the lead for its next item.

## 5. C4 of Lemma 9.3 (09-13): `CornerTwoGonInput`

The lead assigned this lane C4 of PhiPrimeCount (Osin, Appendix, proof of Lemma 9.3).  hull-euler
keeps the assembly.

* Statement: `CornerTwoGonInput` (`Estimating/OsinAppendixEulerCornerTwoGon.lean`, `d0a41c1da`,
  landed unverified).  At most `r = cuts.count` two-gons of `phiMapO S.family E` have a corner in
  their gap at the outer vertex `O`.  hull-euler's `phiPrimeCountInput_of_smallFaces`
  (`OsinAppendixEulerSmallFaces.lean`, `4beca2743`) consumes it unchanged, at
  `E := linkedComponentO S.family a₀`.  `CornerFacesInput` was removed at `4beca2743`, and the lead
  withdrew the bridge to it.
* LANDED `90245333d`: `cornerTwoGonInput` in `Estimating/OsinAppendixEulerCornerTwoGonCount.lean`,
  unconditional, statement unchanged.  Probe `0913-130413-64412` PROBE GREEN with the module BUILT;
  `#audit_axioms` gives `[propext, Classical.choice, Quot.sound]`.  Queued for wiring.
  * An exterior region whose target arc starts at `s` crosses `O` at `B[L - 1 - s]`, where `B` is
    the outer face boundary (`crossO_false_true_of_eq_none`).
  * The outer face lies in no region, so the collapsed face rotation walks along `B`
    (`outer_collapsed_facePerm_pow`).  The rotation of `Φ'_M` is its first return
    (`phiMapO_isRestriction`), so no exterior target arc starts strictly between the two regions
    of a two-gon at `O` (`exists_outer_return`).
  * Target arcs of different regions are disjoint (`eq_of_targetArc_overlap`), so a corner in the
    gap determines the dart at `O` (`exists_gap_offset`, `eq_of_gapHoldsCorner`).
  * The count is double counting over the `r` corners
    (`Finset.card_le_card_of_forall_subsingleton`).
* LANDED `0c42391c2`: `osinCornerTwoGonSection` in
  `Estimating/OsinAppendixEulerCornerTwoGonSection.lean` proves hull-euler's section-level
  `OsinCornerTwoGonSectionStatement` (`6401c70a6`) with `ε₀ = 0` and `ρ₀ = 1`.  Probe
  `0913-130704-80770` PROBE GREEN with the module BUILT, audit
  `[propext, Classical.choice, Quot.sound]`.  Queued for wiring.  The module imports
  `OsinAppendixEulerSection` and the count module, so SmallFaces has no import cycle.
* No literature input, and no hypothesis standing for a cited result.  audit-sec3 independently
  found the statement true.
* `ROSTER-0913.md:559` still names `CornerFacesInput` for C4.  Line 582 records the switch to
  `CornerTwoGonInput`.
* Residual Props in this lane's C4 scope: none.
