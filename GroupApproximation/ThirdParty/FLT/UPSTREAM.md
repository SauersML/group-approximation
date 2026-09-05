# FLT vendoring record

This directory holds a slice of the Lean 4 formalisation of Fermat's Last
Theorem published by Anthropic, vendored for reuse in this development.

- Upstream: <https://github.com/anthropics/fermats-last-theorem>
- Upstream commit: `aa2d8b34692b16c70f699536de0d8e75b9a3e9ef` (fetched 2026-09-05)
- Upstream Lean/Mathlib: Lean `v4.33.1`, Mathlib `v4.33.0`
- Local target: Lean `v4.32.0`, Mathlib pin `81a5d257`
- Upstream license: Apache License 2.0 (`NOTICE` is copied verbatim beside this
  file; `ATTRIBUTION.md` beside this file reproduces the upstream per-file
  notices for the vendored files that carry material from the Imperial College
  London FLT project or from Mathlib). The repository root `LICENSE` is the
  same Apache License 2.0 text.
- Local module root: `GroupApproximation.ThirdParty.FLT`, with the upstream
  layout kept underneath it: `Definitions/Def_*.lean`, `Theorems/Thm_*.lean`,
  `P2M/Sol/S_*.lean`, `P2M/Util.lean`.
- `INDEX.md` beside this file lists every vendored theorem with the one-line
  headline the upstream documentation site gives it, grouped by namespace.

## What was changed

Only import lines. Every `import Theorems.X`, `import Definitions.X`,
`import P2M.X` became `import GroupApproximation.ThirdParty.FLT.<same>`.
Every other byte is as upstream, including the leading `import Mathlib` of
each file and the `set_option maxHeartbeats` bumps.

Declaration namespaces are deliberately NOT prefixed (unlike the HamSandwich
port next door). The proof modules address declarations through the alias
macros `p2m_open` / `p2m_export` / `p2m_alias` defined in `P2M/Util.lean`,
which resolve names by their upstream namespaces; prefixing would silently
turn those aliases into no-ops. The upstream names are FLT-specific or
Mathlib-shim names, so clashes with Mathlib at the local pin are not expected;
clashes with this development's own declarations were not observed by grep.

## Upstream structure

Each `Theorems/Thm_X.lean` states exactly one theorem and proves it by
`p2m_exact_reverting @P2MW.S_X.solution`, where `P2M/Sol/S_X.lean` holds the
proof and its private lemmas inside the namespace `P2MW.S_X`. Definitions live
in `Definitions/Def_*.lean`. `P2M/Util.lean` defines the `p2m_*` command
elaborators; every API it uses (`addAlias`, `activateScoped`, `OpenDecl.simple`,
`privateToUserName?`, `mkPrivateName`, `scopedEnvExtensionsRef`,
`MVarId.revert` with `clearAuxDeclsInsteadOfRevert`) exists in the Lean
`v4.32.0` sources.

## What was selected, and how

Seeds are every upstream theorem whose Lean name lives in a generic,
Mathlib-style namespace (`DoubleComplex`, `CochainCx`, `Matrix`, `Subgroup`,
`IsFreeGroup`, `SimpleGraph`, `QuotientGroup`, `AddCommGroup`, `AddSubgroup`,
`AddMonoidHom`, `Monoid`, `MonoidHom`, `Equiv`, `Function`, `Fin`, `Tuple`,
`Finset`, `Nat`, `Int`, `Multiset`, `Set`, `Finite`, `ENat`, `Complex`,
`AnalyticOnNhd`, `Manifold`, `Homeomorph`, `IsPreconnected`, `ContinuousMap`,
`ContinuousLinearMap`, `InnerProductSpace`, `Orthonormal`, `Summable`,
`MeasureTheory`, `Real`, `Sobolev`, `SchwartzMap`, `VectorFourier`,
`UnitAddTorus`, `AddCircle`, `HaarQuotient`, `HaarMeasure`, `exteriorPower`,
`GradedAlgebra`, `LinearMap`, `LinearEquiv`, `LinearIndependent`, `Module`,
`Submodule`, `TensorProduct`, `DirectSum`, `QuadraticForm`, `Polynomial`,
`MvPolynomial`, `CompleteOrthogonalIdempotents`, `TrivSqZeroExt`,
`IsLocallyConstant`, `Derivation`, `CategoryTheory`, `Topology`,
`TopologicalSpace`, `TopCat`, `IsOpen`, `Representation`, `RestrictedProduct`,
`SetLike`, `IncidenceSystem`), the group-cohomology cup-product Leibniz rule
and the Tate cup product commutativity and associativity, and the definition
files `Def_Mathlib_*`, `Def_Compat_*`, the Haar-measure and Haar-quotient
files, the double complex and bounded cochain tensor files, the cup-product
interfaces, and a few small generic ones.

The vendored set is the transitive import closure of those seeds inside the
upstream repository. A seed was dropped when its closure entered the
number-theory core (any definition file from the modular-forms, Galois,
elliptic-curve, adelic or quaternion-order areas, with more than twenty
modules in the closure), and a short hand list was dropped as well (Deuring
polynomials, quaternion-order lattices, Frey packages, Haar measure on
`GL₂(ℝ)` in Iwasawa coordinates, one heavy `MvPolynomial` coefficient
identity). The upstream theorem
`Matrix.charpolyRev_mul_prod_pow_eq_prod_pow_of_forall_trace_pow_eq`, a
Newton-identity statement, is one of the dropped ones: its closure carries the
Frey-package definitions.

Inventory of the slice:

| item | count |
|---|---|
| theorem modules (`Theorems/`) | 1123 |
| proof modules (`P2M/Sol/`) | 1123 |
| definition modules (`Definitions/`) | 97 |
| macro module (`P2M/Util.lean`) | 1 |
| total modules | 2344 |
| total size | 14.2 MB |

The scripts that produced the slice are kept outside the repository at
`~/flt_borrow_work/` (`closure.py` builds the import graph, `select*.py` pick
the seeds and closure into `selection.json`, `vendor.py` copies and rewrites);
the upstream clone they read was deleted to free disk space and can be
re-cloned with `git clone --filter=blob:none --sparse` at the commit above.

## Status

- NOT compiled here. A user order of 2026-09-05 forbids building or compiling
  any Lean on this machine, and the `.lake` directories were deleted the same
  day. The upstream build was a from-scratch `lake build` on Lean `v4.33.1`
  with every declaration kernel-checked and the axioms of the final theorem
  reported as `[propext, Classical.choice, Quot.sound]`; the slice inherits
  that only modulo the version drift below.
- NOT wired into the root `GroupApproximation.lean`. The aggregator
  `GroupApproximation/ThirdParty/FLT.lean` imports every vendored definition
  and theorem module; wire that one line deliberately once the slice has been
  compiled against the local pin. Until then every module here is an orphan
  in the sense of `scripts/check.py`, exactly as the HamSandwich port was.
- Known hazards for the first compile: the Mathlib drift `v4.33.0 -> pin
  81a5d257` (renamed or moved lemmas; `Definitions/Def_Compat_Mathlib430.lean`
  shows the flavour of the shims the upstream needed for its own drift);
  245 `set_option maxHeartbeats` bumps, which `scripts/check.py` reports as a
  finding class already present on `main`; the library flag
  `-DwarningAsError=true`, which turns any linter warning into an error (the
  proof modules switch off the unused-variable, unused-simp-args and
  unused-section-vars linters themselves); and `import Mathlib` in every file.
- No `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `implemented_by`,
  `extern` or `native_decide` occurs in the slice (lexical scan of every
  vendored file).

## Where the slice is meant to be used

- `DoubleComplex.*`, `CochainCx.*` (bounded double complexes, total
  cohomology, transpose, levelwise functoriality, rows-exact augmentation
  edge isomorphism, exact-columns acyclicity, Euler characteristic, the
  bounded spectral sequence convergence data, and the Künneth theorem for
  bounded cochain complexes over a field): the integral cohomology ring and
  `CP^n` lanes in `AlgTop/` (Künneth, cell filtration bookkeeping).
- `IsDirectLimit` (`Definitions/Def_Mathlib_Algebra_IsDirectLimit.lean`):
  the `K_1` and `K^0` colimits. `Analysis/SequentialGroupColimitDirectLimit.lean`
  identifies the tower colimit of `Analysis/SequentialGroupColimit.lean` as an
  `IsDirectLimit`, which gives it `IsDirectLimit.lift` and `IsDirectLimit.Equiv`.
- `Def_Mathlib_Topology_Algebra_{Group_Units,ContinuousMonoidHom,Module_Quotient,UniformRing}`,
  `Def_Mathlib_Topology_Bases`, `Def_Mathlib_IsModuleTopology`: topological
  groups of units, quotient topologies and continuous homomorphisms, for the
  unitary-component and `U(A)/U_0(A)` material in `Analysis/`.
- `Matrix.*`: the Euler-angle decomposition of `SU(2)`
  (`specialUnitaryGroup_fin_two_eq_diag_mul_rotation_mul_diag`); right-finite
  continuous functions on `U(n)` and `O(n)` are polynomial
  (`UnitaryGroup_exists_polynomial_eq_of_continuous_of_rightFinite` and the
  orthogonal twin, Peter-Weyl adjacent); QR and Iwasawa-type decompositions
  (`exists_upperTriangular_pos_diag_mul_orthogonal_eq_of_det_ne_zero`, its
  smooth version, `exists_specialLinearGroup_mul_upperTriangular`); the
  elementary-matrix factorisation
  `exists_list_prod_elementary_eq_diagonal_of_det_map_mul_eq_one` (the
  Whitehead-lemma territory of `K_1`); Selberg's lemma
  (`ProjGenLinGroup_exists_torsionFree_normal_subgroup_finiteIndex_of_fg_charZero`,
  `GeneralLinearGroup_exists_normal_relIndex_ne_zero_forall_isOfFinOrder_imp_eq_one_of_fg`)
  and Minkowski's lemma
  (`GeneralLinearGroup_eq_one_of_isOfFinOrder_of_forall_sub_one_mem_of_ne`);
  free subgroups of `SL₂` by ping-pong
  (`SpecialLinearGroup_exists_generators_free_mod_neg_one_of_forall_trace_ne`,
  `SpecialLinearGroup_nonempty_freeGroupBasis_map_quotient_center_of_forall_trace_ne`);
  traces of powers (`trace_pow_eq_sum_pow`, `trace_pow_eq_of_trace_eq_of_det_eq`).
  Consumers: `GGT/`, `Sofic/`, `Kazhdan/`, the `K_1` files in `Analysis/`.
- Group theory: `Monoid.CoprodI_nonempty_freeGroupBasis_fin_kuroshRank`
  (free bases of finite-index subgroups of free products, with the Kurosh
  rank), `IsFreeGroup.surjective_transfer_and_transfer_eq_one_iff_mem_closure`,
  `SimpleGraph.exists_walkConnected_transversal_of_preconnected` (Schreier
  transversals), `Subgroup.exists_exact_fundamental_domain_of_secondCountableTopology`,
  `Subgroup.card_orbitRelQuotient_mul_card_eq_index`,
  `Subgroup.exists_le_normal_subgroupOf_relIndex_ne_zero_torsionFree_of_relIndex_ne_zero`,
  `AddSubgroup.addGroup_fg_of_le_of_addGroup_fg`, the `AddCommGroup` torsion
  structure theorems, discrete subgroups of `ℝⁿ`
  (`AddSubgroup.exists_continuousLinearEquiv_prod_mem_iff_of_discreteTopology`):
  `GGT/` and `Sofic/`.
- `Complex.*`: the argument principle
  (`circleIntegral_mul_deriv_div_sub_eq_sum_analyticOrderNatAt`), the residue
  theorem for simple poles, Jensen's inequality
  (`AnalyticOnNhd.log_norm_le_circleAverage_log_norm`), polar coordinates on
  balls: winding numbers and the degree on `S¹`, hence the `K`-theory of `S¹`
  and the integral normalisation of the Chern character in `KTheory/`.
- Compact operators: convolution operators on `L²` of a compact group are
  compact and symmetric (`MeasureTheory.L2_exists_convolutionCLM_isCompactOperator*`,
  `L2_convolutionCLM_isSymmetric_of_conj_neg`), eigenspaces of a compact
  operator are finite dimensional
  (`Submodule.finiteDimensional_of_isCompactOperator_of_forall_apply_eq`),
  Hilbert-Schmidt kernel operators
  (`Definitions/Def_Mathlib_MeasureTheory_Function_L2KernelOperator.lean`),
  commuting operators preserve eigenspaces and their orthogonal complements
  (`ContinuousLinearMap.map_eigenspace_orthogonal_le_of_commute`,
  `orthogonal_iSup_eigenspace_ne_zero_eq_ker`): `Analysis/CompactIntegralOperator`
  and the Peter-Weyl material.
- `Representation.*`: complete reducibility for continuous representations of
  compact groups (`exists_isCompl_forall_mem_of_compactSpace_of_continuous`),
  absolutely irreducible representations
  (`isAbsolutelyIrreducible_iff_isIrreducible_and_surjective_algebraMap_end`,
  `span_range_eq_top_of_isAbsolutelyIrreducible`), Schur-type centraliser
  statements, Brauer-Nesbitt in characteristic zero
  (`Definitions/Def_RepTheory_BrauerNesbitt_TraceCharZero.lean`),
  `p`-group fixed vectors: finite-group representation theory in `Sofic/`.
- Measure theory: Haar measures on quotients (`HaarQuotient.*`), modular
  characters of automorphisms and rings (`Definitions/Def_HaarMeasure_HaarChar_*`),
  fundamental domains, Haar measure on restricted products, continuity of
  translation in `L²`: `Analysis/CompactHaar` and the amenability material.
- `LinearMap.*` exact-sequence rank counting
  (`finite_and_sum_finrank_eq_of_exact_of_exact_of_exact`,
  `finrank_even_eq_finrank_odd_of_nineTerm_exact`, `exact_dualMap_of_exact`,
  `finrank_ker_sub_finrank_quotient_range_eq_add_of_exact`): long exact
  sequence bookkeeping in `AlgTop/`.
- Group cohomology: the cup product on inhomogeneous cochains with its
  Leibniz rule (`Definitions/Def_GroupCohomology_{CochainCup,CupProduct}.lean`,
  `groupCohomology.d_cochainCup_apply`), the graded cup-product interface
  (`Def_GroupCohomology_IsGradedCupProduct.lean`) and the Tate cup product's
  commutativity and associativity (`Rep.IsTateCupProduct.cup_comm`,
  `cup_assoc`): a worked model for the graded commutativity that
  `AlgTop/CupProduct.lean` leaves open.
- `exteriorPower.*` (top exterior power of an endomorphism is multiplication
  by the determinant, base change), depth and Auslander-Buchsbaum
  (`Module.depth_*`, `Module.free_of_depth_eq_ringKrullDim_of_isRegularLocalRing`),
  `Polynomial.*`, `MvPolynomial.*`: general algebra, no current consumer.
