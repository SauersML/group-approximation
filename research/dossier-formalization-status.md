---
rg: 2
id: dossier-formalization-status
kind: claim
title: Formalization ledger for the multi-mover / ascending-HNN dossier
---

Target: `Downloads/formalize/full_proof_dossier_multi_mover_hnn_soficity(4).md`
(8489 lines, sections 0-54).  This card tracks, section by section, what is
already machine-checked in this repository, what is newly formalized, and what
remains.

Status codes: **DONE-PRE** already in-repo before this pass; **DONE-NEW**
formalized in this pass; **TODO** not yet formalized.

| Dossier | Statement | Status | Lean location |
|---|---|---|---|
| 3.1 | `‖D‖_F² ≤ rank D · ‖D‖_op²` | DONE-PRE | `Sofic/InvolutionRankMass.matMass_le_rank_mul_sq_opNorm` |
| 3.2 | nearby projections have equal rank | DONE-PRE | `Sofic/InvolutionRankMass.rank_eq_of_projections_close` |
| 3.3 | commuting involutions: `T³=4T`, `‖u-v‖_F²=4·rank` | DONE-PRE | `Sofic/InvolutionRankMass` (`sub_mul_sub_mul_sub`, `matMass_sub_eq_four_mul_rank`) |
| 4.1 | property (T) ⇒ finitely generated | TODO | |
| 4.2 | finitely many movers | TODO | |
| 5.1-5.3 | max-displacement word estimate | DONE-NEW | `Sofic/MaxDisplacement` (`dist_inv_smul_le`, `dist_smul_le_of_mem_closure`, `exists_infinite_constant_argmax`) |
| 6.1 | subsequence vanishing ≠ corona vanishing | DONE-NEW | `Sofic/CoronaSubsequence.exists_vanishing_on_subsequence_not_tendsto_zero` |
| 7.1-7.2 | finite block amplification; corrected (iii) removal | TODO | |
| 2.4 | GKEP sofic action (Definition 2.1) | DONE-NEW | `Sofic/SoficAction.SoficActionModel`, `IsSoficAction` |
| 9.1-9.3 | ascending normal form, `N = ker χ`, `G = N ⋊ ℤ` | DONE-PRE | `Algebra/MappingTelescope`, `Sofic/MarkedCompressionGroup.Vertical` |
| 9.4 | ascending HNN is not property (T) | DONE-NEW | `Kazhdan/IntegerNotKazhdan.not_hasKazhdanPropertyT_multiplicative_int`, `Sofic/AscendingHNNNotKazhdan.not_hasKazhdanPropertyT_vertical` |
| 10.1-10.3 | explicit interval Folner sets for `G/Γ` | TODO | |
| 11.1-11.3 | Γ sofic ⇒ G sofic | DONE-PRE | `Sofic/SoficDirectedUnion`, `Sofic/SoficIntegerExtension`, `Sofic/SoficTelescope` |
| 12.1 | cyclic extension permanence for sofic actions | DONE-NEW | `Sofic/SoficActionCyclicExtension.isSoficAction_semidirect`, on the permutation layer of `Sofic/CyclicStack` |
| 13.1 | consecutive levels have index `D` | DONE-PRE | `Sofic/MappingTelescopeFiniteOrbits.level_succ_relIndex_eq` |
| 13.2 | every telescope level has finite orbits on `G/Γ` | DONE-PRE | `Sofic/MappingTelescopeFiniteOrbits.finite_verticalLevel_orbit` |
| 13.3 | finite-orbit actions are sofic, exact models | DONE-NEW | `Sofic/SoficActionFiniteOrbits.isSoficAction_of_finite_orbits` |
| 13.4 | increasing unions preserve action soficity | DONE-NEW | `Sofic/SoficActionFiniteOrbits.isSoficAction_of_locally_finite_orbits`; general form `Sofic/SoficAction.isSoficAction_of_subgroup_cover` |
| 13.5 | finite-index HNN coset action is sofic | DONE-NEW | `Sofic/AscendingHNNCosetActionSofic.isSoficAction_vertical_cosets` |
| 14.1 | sofic wreath criterion | TODO | needs 29.6 |
| 29 | generalized-wreath soficity from first principles | TODO | |
| 30.2 | finite-index coset actions are sofic | DONE-NEW | `Sofic/SoficActionExamples.isSoficAction_quotient_of_finiteIndex` |
| 30.3 | Chabauty closure of transitive sofic actions | DONE-NEW | `Sofic/SoficActionChabauty.isSoficAction_quotient_of_approximable` |
| 30.5 | separable stabiliser ⇒ transitive coset action sofic (the LERF mechanism) | DONE-NEW | `Sofic/SoficActionChabauty.isSoficAction_quotient_of_separable` |
| 30.4, 30.6, 30.7 | orbit gluing; amenable and LERA actions | TODO | orbit gluing needs sofic actions on disjoint unions |
| 43.3 | generation bound for the wreath product | DONE-NEW | `Algebra/PermutationalWreathSimple.wreath_eq_closure` |
| 52.2 | simple quotients of a lamp group come from one coordinate | DONE-NEW | `Algebra/PermutationalWreathSimple.exists_site_bijective_of_simple_quotient` |
| 31.1-31.2 | universally action-sofic HNN theorem | DONE-NEW | `Sofic/AscendingHNNCosetActionSofic` (`UniversallyActionSofic`, `isSoficAction_vertical_cosets_of_uas`) |
| 33 | involutive compression collapse theorem | DONE-PRE | `Sofic/InvolutionCollapseEndpoint` |
| 36.1-36.3 | projection collapse, torsion collapse | DONE-PRE | `Sofic/ProjectionCompressionCollapse`, `Sofic/TorsionSpectralCollapse` |
| 36.4 | one-site lamp is a commuting-orbit witness for **any** lamp group; the defect is nontrivial | DONE-NEW | `Algebra/PermutationalWreath` (`conj_single_commute`, `single_mul_single_inv_ne_one`) |
| infra | permutational wreath product `K^{(X)} ⋊ G` for arbitrary, possibly nonabelian, `K` | DONE-NEW | `Algebra/PermutationalWreath` (`lampSubgroup`, `Lamp`, `Lamp.single`, `lampAut`, `Wreath`) |
| 37.7B | residually finite ⇒ MF | DONE-PRE | `Sofic/OperatorMFPositiveControls.isOperatorMF_of_residuallyFinite` |
| 37.7C | subgroups of MF groups are MF | DONE-PRE | `Sofic/OperatorMFPositiveControls.IsOperatorMF.subgroup` |
| 43.4, 54.2 | the lamp group itself is residually finite for finite `K` | DONE-NEW | `Algebra/PermutationalWreath.lamp_isResiduallyFinite` |
| 37 | telescope-kernel collapse, exact MF radical | TODO (partial in-repo) | |
| 39 | concrete affine base, index 8, RF skeleton | DONE-PRE | `Sofic/LiteralBaseDoublingIndex`, `Sofic/CommutingLampCollapse`, `Monsters/ExplicitLinearModel` |
| 41-43 | equality of MF / f.d. / finite residuals | TODO | |
| 42.7 | intersection of all finite-index subgroups = finite residual | DONE-NEW | `Algebra/FiniteResidual.finiteResidual_eq_normalFiniteResidual` |
| 46.5, 49.2B | residual finiteness is a commensurability invariant | DONE-NEW | `Algebra/FiniteResidual` (`IsResiduallyFinite.subgroup`, `isResiduallyFinite_of_finiteIndex_subgroup`) |
| 46.1-46.4 | Malcev; all-fields linear residual; nonlinearity | TODO | |
| 49 | finite-index induction of the MF radical | TODO (MF case) | |
| 49.4 | finite-index heredity of the finite residual | DONE-NEW | `Algebra/FiniteResidual.mem_finiteResidual_subgroup_iff` |
| 50.1 | functoriality / full invariance of the finite residual | DONE-NEW | `Algebra/FiniteResidual.map_finiteResidual_le` |
| 51.1 | simple lamps: one relation generates the whole lamp subgroup | DONE-NEW | `Algebra/PermutationalWreathSimple.lamp_le_normalClosure_single`, on `Lamp.mem_closure_singles` |
| 52 | alternating-lamp noncommensurable family | TODO | |
| 53 | four-dimensional rational envelope | TODO | |
| 54.2 | MF not closed under split extensions | TODO | |
| 54.3 | wreath examples are not finitely presented | TODO | |

## Notes

* The two new modules are deliberately universe-polymorphic in the acted-on set,
  so `permDist` is redeveloped rather than reusing the `Type`-valued
  `FiniteModel` bundle of `Sofic.Sofic`.
* `exists_soficActionModel_of_finiteOrbits` proves 13.3 and 13.4 in one step:
  because the model is built for the ambient group with the map extended by the
  identity outside the finite-orbit subgroup, no transfer of models between
  different acting groups is ever needed.
* Root import for the two new modules is still pending; they are currently built
  as orphans by `scripts/msi-build.sh`.
