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
| 5.1-5.3 | max-displacement word estimate | TODO | |
| 6.1 | subsequence vanishing ≠ corona vanishing | TODO | |
| 7.1-7.2 | finite block amplification; corrected (iii) removal | TODO | |
| 2.4 | GKEP sofic action (Definition 2.1) | DONE-NEW | `Sofic/SoficAction.SoficActionModel`, `IsSoficAction` |
| 9.1-9.3 | ascending normal form, `N = ker χ`, `G = N ⋊ ℤ` | DONE-PRE | `Algebra/MappingTelescope`, `Sofic/MarkedCompressionGroup.Vertical` |
| 9.4 | ascending HNN is not property (T) | TODO | |
| 10.1-10.3 | explicit interval Folner sets for `G/Γ` | TODO | |
| 11.1-11.3 | Γ sofic ⇒ G sofic | DONE-PRE | `Sofic/SoficDirectedUnion`, `Sofic/SoficIntegerExtension`, `Sofic/SoficTelescope` |
| 12.1 | cyclic extension permanence for sofic actions | TODO | (hardest remaining piece of the headline chain) |
| 13.1 | consecutive levels have index `D` | DONE-PRE | `Sofic/MappingTelescopeFiniteOrbits.level_succ_relIndex_eq` |
| 13.2 | every telescope level has finite orbits on `G/Γ` | DONE-PRE | `Sofic/MappingTelescopeFiniteOrbits.finite_verticalLevel_orbit` |
| 13.3 | finite-orbit actions are sofic, exact models | DONE-NEW | `Sofic/SoficActionFiniteOrbits.isSoficAction_of_finite_orbits` |
| 13.4 | increasing unions preserve action soficity | DONE-NEW | `Sofic/SoficActionFiniteOrbits.isSoficAction_of_locally_finite_orbits` |
| 13.5 | finite-index HNN coset action is sofic | TODO | needs 12.1 |
| 14.1 | sofic wreath criterion | TODO | needs 29.6 |
| 29 | generalized-wreath soficity from first principles | TODO | |
| 30 | every action of a LERF / LERA group is sofic | TODO | |
| 31 | universally action-sofic HNN theorem | TODO | |
| 33 | involutive compression collapse theorem | DONE-PRE | `Sofic/InvolutionCollapseEndpoint` |
| 36.1-36.3 | projection collapse, torsion collapse | DONE-PRE | `Sofic/ProjectionCompressionCollapse`, `Sofic/TorsionSpectralCollapse` |
| 37 | telescope-kernel collapse, exact MF radical | TODO (partial in-repo) | |
| 39 | concrete affine base, index 8, RF skeleton | DONE-PRE | `Sofic/LiteralBaseDoublingIndex`, `Sofic/CommutingLampCollapse`, `Monsters/ExplicitLinearModel` |
| 41-43 | equality of MF / f.d. / finite residuals | TODO | |
| 46 | Malcev; all-fields linear residual; nonlinearity | TODO | |
| 49 | finite-index induction of the MF radical | TODO | |
| 50 | full invariance / functoriality of the radical | TODO | |
| 51 | simple lamps: one relation generates the radical | TODO | |
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
