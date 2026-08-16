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
| 4.1 | property (T) ⇒ finitely generated | DONE-PRE | `Kazhdan/KazhdanFiniteGeneration.exists_symmetric_generating_finset` (same quasi-regular argument as the dossier) |
| 4.2 | finitely many movers | DONE-NEW | `Sofic/MoverGeneration` (`closure_stabilizer_union_movers`, `movers_finite`) |
| 5.1-5.3 | max-displacement word estimate | DONE-NEW | `Sofic/MaxDisplacement` (`dist_inv_smul_le`, `dist_smul_le_of_mem_closure`, `exists_infinite_constant_argmax`) |
| 6.1 | subsequence vanishing ≠ corona vanishing | DONE-NEW | `Sofic/CoronaSubsequence.exists_vanishing_on_subsequence_not_tendsto_zero` |
| 7.1-7.2 | finite block amplification; corrected (iii) removal | TODO | |
| 2.4 | GKEP sofic action (Definition 2.1) | DONE-NEW | `Sofic/SoficAction.SoficActionModel`, `IsSoficAction` |
| 9.1-9.3 | ascending normal form, `N = ker χ`, `G = N ⋊ ℤ` | DONE-PRE | `Algebra/MappingTelescope`, `Sofic/MarkedCompressionGroup.Vertical` |
| 9.4 | ascending HNN is not property (T) | DONE-NEW | `Kazhdan/IntegerNotKazhdan.not_hasKazhdanPropertyT_multiplicative_int`, `Sofic/AscendingHNNNotKazhdan.not_hasKazhdanPropertyT_vertical` |
| 10.1-10.3 | explicit interval Følner sets for `G/Γ` | DONE-NEW | `Sofic/AscendingHNNFolner` (`ray`, `smul_ray_eq`, `exists_folner_interval`); the ray is indexed by `ℤ`, which removes the near-end case analysis |
| 11.1-11.3 | Γ sofic ⇒ G sofic | DONE-PRE | `Sofic/SoficDirectedUnion`, `Sofic/SoficIntegerExtension`, `Sofic/SoficTelescope` |
| 12.1 | cyclic extension permanence for sofic actions | DONE-NEW | `Sofic/SoficActionCyclicExtension.isSoficAction_semidirect`, on the permutation layer of `Sofic/CyclicStack` |
| 13.1 | consecutive levels have index `D` | DONE-PRE | `Sofic/MappingTelescopeFiniteOrbits.level_succ_relIndex_eq` |
| 13.2 | every telescope level has finite orbits on `G/Γ` | DONE-PRE | `Sofic/MappingTelescopeFiniteOrbits.finite_verticalLevel_orbit` |
| 13.3 | finite-orbit actions are sofic, exact models | DONE-NEW | `Sofic/SoficActionFiniteOrbits.isSoficAction_of_finite_orbits` |
| 13.4 | increasing unions preserve action soficity | DONE-NEW | `Sofic/SoficActionFiniteOrbits.isSoficAction_of_locally_finite_orbits`; general form `Sofic/SoficAction.isSoficAction_of_subgroup_cover` |
| 13.5 | finite-index HNN coset action is sofic | DONE-NEW | `Sofic/AscendingHNNCosetActionSofic.isSoficAction_vertical_cosets` |
| 14.1 | sofic wreath criterion for finite-index self-embeddings | DONE-NEW | `Sofic/AscendingHNNWreathSofic.isSofic_wreath_cosets`, with `isSofic_vertical` assembling Section 11 |
| 29.3 | finite products of sofic groups are sofic | DONE-NEW | `Sofic/SoficPiProduct` (`isSofic_pi`, `isSofic_prod`), on the exact agreement identity `one_sub_hammingDistance_piPerm` |
| 29.1, 29.2 | normalized Hamming metric; ultraproduct criterion | DONE-PRE | `Sofic/Sofic`, `Sofic/SoficUltraproduct` |
| 29.4 | the permutation layer of a wreath model | DONE-NEW | `Sofic/WreathPermLayer` (`fiberPerm`, `hammingDistance_fiberPerm` and its two estimates) |
| 29.6 | full generalized-wreath theorem | DONE-NEW | `Sofic/GeneralizedWreathSofic.isSofic_wreath`; the charted-lamp transport (29.3) is `Sofic/WreathChartLamp.chartLamp_congr`.  Proved with permutation models directly, so no metric ultraproduct of wreath targets is needed |
| 30.2 | finite-index coset actions are sofic | DONE-NEW | `Sofic/SoficActionExamples.isSoficAction_quotient_of_finiteIndex` |
| 30.3 | Chabauty closure of transitive sofic actions | DONE-NEW | `Sofic/SoficActionChabauty.isSoficAction_quotient_of_approximable` |
| 30.5 | separable stabiliser ⇒ transitive coset action sofic (the LERF mechanism) | DONE-NEW | `Sofic/SoficActionChabauty.isSoficAction_quotient_of_separable` |
| 30.4 | orbit gluing: sofic actions are closed under disjoint unions | DONE-NEW | `Sofic/SoficActionSum.isSoficAction_sum` (two pieces); arbitrary orbits in `Sofic/SoficActionOrbits.isSoficAction_of_stabilizers`, via injective equivariant covers |
| 30.5, 30.7 | separable / LERA groups are universally action-sofic | DONE-NEW | `Sofic/SoficActionOrbits` (all subgroups separable / LERA / amenable) and `Sofic/SoficActionApproximationBelow` (`universallyActionSofic_of_fg_separable`, `universallyActionSofic_of_fg_lera`) for the actual finitely generated hypotheses, via approximation of a stabilizer from below |
| 15.1 | LERF base: coset action sofic for arbitrary self-embedding | DONE-NEW | `Sofic/AscendingHNNWreathSofic` (`isSoficAction_vertical_cosets_of_fg_separable`, `isSofic_wreath_cosets_of_fg_separable`) |
| 30.6 | every action of an amenable group is sofic | DONE-NEW | `Sofic/AmenableActionSofic` (`isSoficAction_of_amenable_surjHom`, `isSoficAction_of_isAmenable`), Følner sets via `exists_folner` |
| 30.6 co-amenable | strongly co-amenable subgroups have sofic coset actions | DONE-NEW | `Sofic/CoAmenableActionSofic` (`StronglyCoAmenable`, `isSoficAction_quotient_of_stronglyCoAmenable`, `normalCore_inf`) |
| 30.7 | LERA groups: transitive actions are sofic | DONE-NEW | `Sofic/CoAmenableActionSofic.isSoficAction_quotient_of_isLERA`; the non-transitive case is closed in `Sofic/SoficActionOrbits` |
| 34.1 | the witness site `tΓ` has stabiliser exactly `α(Γ)` in `Γ` | DONE-NEW | `Sofic/AscendingHNNStabilizer.smul_tSite_eq_iff` |
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
| 36.5-36.8 | radical pullback through a defect quotient; exact radical; defect saturation | DONE-NEW | `Sofic/CoronaRadicalPullback` (`coronaMFResidual_eq_comap`, `coronaMFResidual_eq_of_quotient_isOperatorMF`, `not_isOperatorMF_of_coronaMFResidual_eq_top`) |
| 41.3 first inclusion | `Rad_MF ≤ Rad_fd` | DONE-PRE | `Sofic/MatricialStabilityRadical.actualCoronaMFResidual_le_fdUnitaryResidual` |
| 37 union step | increasing forced-defect kernels stay inside the radical | DONE-NEW | `Sofic/MoverGeneration.coronaMFResidual_iSup_le` |
| 37 | telescope-kernel collapse, exact MF radical | TODO (partial in-repo) | 36.5 supplies the pullback step, 36.7 the exact-radical step; what remains is the concrete pushforward tower |
| 54.2 lamp side | the lamp group is locally finite for finite `K` | DONE-NEW | `Algebra/PermutationalWreath.suppIn_finite` |
| 39 | concrete affine base, index 8, RF skeleton | DONE-PRE | `Sofic/LiteralBaseDoublingIndex`, `Sofic/CommutingLampCollapse`, `Monsters/ExplicitLinearModel` |
| 41.3 second inclusion | `Rad_fd ≤ Res_fin` | DONE-NEW | `Sofic/FiniteDimensionalResidual.fdUnitaryResidual_le_finiteResidual`, on the faithful coset permutation representation `permUnitaryHom` |
| 41.1 | residual finiteness of the exact quotient (product and embedding steps) | DONE-NEW | `Sofic/ThreeRadicalsCoincide` (`IsResiduallyFinite.prod`, `IsResiduallyFinite.of_injective`, `isResiduallyFinite_of_embed_prod`) |
| 41.2 | the three radicals coincide | DONE-NEW | `Sofic/ThreeRadicalsCoincide.three_radicals_eq`, from a single assumed inclusion `ker Φ ≤ Rad_MF` |
| 42.7 | intersection of all finite-index subgroups = finite residual | DONE-NEW | `Algebra/FiniteResidual.finiteResidual_eq_normalFiniteResidual` |
| 46.5, 49.2B | residual finiteness is a commensurability invariant | DONE-NEW | `Algebra/FiniteResidual` (`IsResiduallyFinite.subgroup`, `isResiduallyFinite_of_finiteIndex_subgroup`) |
| 46.1-46.4 | Malcev; all-fields linear residual; nonlinearity | TODO | |
| 49.1, 49.2 | induction from a finite-index subgroup; exact heredity | DONE-NEW (f.d. case) | `Sofic/InducedFiniteDimensional` (`indHom`, `fdUnitaryResidual_subgroupOf`); the whole construction runs on one coefficient function `coeff π a b`, so no dependent case distinction enters a matrix index.  The MF (corona) case still needs the amplification isomorphism of (49.4) |
| 49.4 | finite-index heredity of the finite residual | DONE-NEW | `Algebra/FiniteResidual.mem_finiteResidual_subgroup_iff` |
| 50.1 | functoriality / full invariance of the finite residual | DONE-NEW | `Algebra/FiniteResidual.map_finiteResidual_le` |
| 51.1 | simple lamps: one relation generates the whole lamp subgroup | DONE-NEW | `Algebra/PermutationalWreathSimple.lamp_le_normalClosure_single`, on `Lamp.mem_closure_singles` |
| 52.1 | `Aₙ` is simple for `n ≥ 5` | DONE-PRE | Mathlib `alternatingGroup.isSimpleGroup` (available for `5 ≤ Nat.card α`, not only `A₅`) |
| 52.3 | the alternating lamps are pairwise non-isomorphic, so the hidden simple type is an invariant | DONE-NEW | `Algebra/PermutationalWreathSimple` (`nonempty_mulEquiv_of_lamp_mulEquiv`, `alternating_lamp_not_mulEquiv`) |
| 53 | wreath split quotient: `ker(rightHom) = ` lamp subgroup | DONE-NEW | `Algebra/WreathSplitQuotient` (`ker_rightHom_eq_lampRange`, `ker_comp_rightHom_eq_lampRange`) |
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
* Every module listed here is imported by the root `GroupApproximation.lean`, so
  the kernel audit and `lake build` see all of it; orphan modules are invisible to
  both and must never be left unimported.
