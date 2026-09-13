# Lane ms-core-3: sentence ledger for tex 1459–1515 (eq:clopen-defect-pair, lem:transient-matrices)

CLAIM lem:involution-localization, F₂ matrix clause (tex 1689–1693) — module path set once ct-involution's split statement lands
- Main's item (b): help ct-involution by direct agreement (2026-09-13 ~17:20).
- Step 1 (support and wandering cover) is ct-involution's: `Dynamics/TransientSupport.lean`, attic 694740ca6, probing.
  This lane's earlier step-1 proposal is WITHDRAWN, and `TransientSupportCover.lean` was never created.
- ct-involution splits `PrintedInvolutionLocalization` into a ring clause and a matrix clause, and sends the landed
  statement names first. Target: `matrixClause_of_ringClause (hring) (hel : CoreKernelElementaryStatement) : <matrix clause>`,
  with the kernel spelled through ct-rank-budget's `Units.map (RingHom.mapMatrix (restrict T (ZMod 2) …))`.
- Route (tex 1689–1693): put the entries of `G − 1` and `G⁻¹ − 1` into F; entrywise conjugation by the scalar `w I_n` gives
  deviations `p_C a p_C` with `a ∈ I`; `w I_n ∈ EL_n` for `n ≥ 2` from `hel`.
- No Lean is drafted until those names land.

## Progress log

- 09-13 ~17:35: ct-involution landed the split statement at 8b453b096 (Dynamics/InvolutionLocalizationStatement).
- 09-13 18:10: **LANDED e131463f7**, `GroupApproximation/Dynamics/InvolutionLocalizationMatrix.lean`; probe 0913-181027-16647 is
  GREEN with a BUILT line, and all six declarations depend on axioms [propext, Classical.choice, Quot.sound]. Queued for wiring.
  - Endpoint `ClopenCrossedProduct.involutionLocalizationMatrixClause_of_ringClause (hring : InvolutionLocalizationRingClause)
    (hel : CoreKernelElementaryStatement) : InvolutionLocalizationMatrixClause`.
  - Pieces: `exists_finset_deviations`, `deviation_mem_coreTransientIdeal`, `map_entry_sub_one_eq_zero`,
    `exists_involution_zmodTwo`, `scalar_conj_apply`, `scalar_conj_sub_one_apply`, `restrict_eq_one_of_sub_one_mem`,
    `scalar_mem_ker_of_map_eq_one`.
  - Inputs, checked on origin (lead correction ~18:15):
    - `InvolutionLocalizationRingClause` is CLOSED: `ClopenCrossedProduct.involutionLocalizationRingClause_closed`
      (ct-involution 0011a8b3a, Dynamics/InvolutionLocalizationRingClosed, `#audit_closed_axioms`), through
      `chainCoreDefectCoverStatement_holds`.
    - `CoreKernelElementaryStatement` is the only open input. ms-units' `coreKernelElementaryStatement_of_matricial`
      (eaa87e3a1, Dynamics/CoreKernelFTwo) reduces it to `TransientIdealLocallyMatricialFTwoStatement`, which has no
      producer on main. Its owner is chain-matricial (module 5), with second starts ms-core-4 and ms-units.
    - The local finiteness of `K_1(I)` (tex 1693) belongs to chain-radical.
  - Census rows `50c5dd41dff4`, `5c06eec5555b` and `1c114e2c4209` are graded `partial` over that one open Prop
    (`metadata/nm-census-rows/ms-core-3.tsv`).
- Build trap: the chain-core statement modules do not import `Mathlib.Algebra.Field.ZMod`. Without `Field (ZMod 2)` in
  scope, specializing a `∀ k [Field k]` statement at `ZMod 2` makes the unifier unfold `ZMod 2` arithmetic
  (`Nat.rec` ~29k, `Fin.add` ~5.6k in the diagnostics), and it times out even at 1M heartbeats. Fix: import the module and use
  `haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩`.

Wave-2 range lane of session `nonsofic-existence-49` (brief C; `notes/nm-swarm/reports/ct-lead.md`).  Snapshot:
origin/main 19d96c2c5 (tex unchanged since 73a84cd9c).  Keys and paragraph lines come from the census merge
0913-160921 (`sentence_census.py` over the current tex); owners from the census `CHAIN_OWNERS` map and the lane
reports.

## Ledger

Every sentence of tex 1459–1515 and its owner.  "carried" = the planned or landed carrier named by the owner.
No sentence of this range is unowned, so this lane builds nothing here.

| key | tex | sentence (abridged) | owner | carrier state (origin 19d96c2c5) |
|---|---|---|---|---|
| `549aa93e832f` | 1456–1461 | "They avoid Y: for any compressed clopen P, set p, d and calculate" + display eq:clopen-defect-pair `s=up+1−p, t=pu⁻¹+1−p, ts=1, st=1−d` | chain-core | row `formalized`: `printedDefectsAvoidY`, `defectT_mul_defectS`, `defectS_mul_defectT` (Dynamics/ClopenDefectPair root-imported; Dynamics/ClopenDefectRestriction landed a55be3025/bc8b7c369, queued for wiring, not yet root-reachable) |
| `bba38420cf8b` | 1462 | "Restriction to the directly finite ring R_Y forces d\|_Y = 0." | chain-core | row `formalized`: `printedRestrictionKillsDefect`, `restrict_defectD_eq_zero` (ClopenDefectRestriction, queued for wiring) |
| `eda117e756e6` | 1465–1467 | definition: locally matricial; subalgebras may have their own local identities | chain-matricial | `IsLocallyMatricialIn`, `IsLocallyMatricial` (Algebra/LocallyMatricial, landed 839935133, queued for wiring); model tests `isLocallyMatricial_matrix`, `not_isLocallyMatricialIn_squareZero` |
| `7ff20576d4cf` | 1469–1475 | exact sequence `0 → I → R_X → R_Y → 0`, `I = LC_c(X∖Y,k) ⋊_T ℤ` | chain-matricial | module 6 draft Dynamics/TransientIdealExact.lean (disk, unlanded): `transientIdeal`, `mem_transientIdeal_iff_forall_coeff`; `restrict_surjective` planned |
| `f0c16e5c8519` | 1476–1478 | I locally matricial, generated by the defect indicators | chain-matricial | planned `isLocallyMatricialIn_transientIdeal` (module 5), `transientIdeal_eq_span_defects` (module 6) |
| `910136e6e66d` | 1482 | LC functions on a closed subset extend by finite clopen partitions | theoremc-retire (module 2) | Topology/LocallyConstantClosedExtension.lean (disk, in theoremc-retire.files) |
| `c05b0ec8b821` | 1482 | restriction kernel = compactly supported in the complement | theoremc-retire (module 2) | `comap_val_eq_zero_iff_support_subset_compl` (planned, same module) |
| `97e43ae93d14` | 1482 | Laurent normal forms give exactness | chain-matricial | `mem_transientIdeal_iff_forall_coeff` (draft) |
| `2546c17d9884` | 1482 | defect translates cover the complement; clopen subdivision gives generation | chain-matricial | `ker_restrict_le_of_forall_defectD` (planned, module 6) |
| `e60c16639f70` | 1489 | Put U = X∖Y | chain-matricial | binder `U := Yᶜ` (assembly) |
| `f5264e48f943` | 1489 | compact C ⊂ U: m wandering clopen sets; each orbit meets C ≤ m times | chain-matricial | `exists_wandering_clopen_cover`, `ncard_orbit_inter_le` (module 5, planned) |
| `4244fb3c658b` | 1489 | U has no periodic points | chain-matricial | `zpow_apply_ne_self_of_mem_compl` (module 5, planned) |
| `34e1eeff13be` | 1489 | finite subsets of I as combinations of compact clopen partial shift graphs | chain-matricial | `transientIdeal_eq_span_graphs` (module 5, planned) |
| `cd20a742dd3c` | 1489 | include inverse partial shifts; C = union of sources and ranges | theoremc-retire (module 4) | Dynamics/PartialShiftClasses.lean (not started on disk) |
| `1687471008a1` | 1489 | generated relation has classes of size ≤ m | theoremc-retire (module 4) | `card_reachableExponents_le` (planned) |
| `ff376e50f433` | 1489 | erasing loops: paths of length ≤ m − 1 | theoremc-retire (module 4) | `reachableExponents_eq_of_le` (planned) |
| `a3598c08b42c` | 1489 | freeness makes the arrow between related points unique | theoremc-retire (module 4) | `zpow_injOn_orbit` (planned) |
| `741b64286b55` | 1489 | the relation is finitely many partial shifts with compact clopen domains | theoremc-retire (module 4) | `isClopen_setOf_reachableExponents_eq` (planned) |
| `1d0f9a56866c` | 1502 | finite clopen partition separating distinct points in each class | theoremc-retire (module 4) | `levelPartition`, `levelPartition_separates` (planned) |
| `fd026a61f84f` | 1502 | order the atoms; representative in the first occupied atom | theoremc-retire (module 4) | `baseSet` (planned) |
| `46f3810145ee` | 1502 | the representative set is clopen | theoremc-retire (module 4) | `isClopen_baseSet` (planned) |
| `5079b22a3633` | 1502 | refine by occupied atoms, shift exponents, coefficient values | theoremc-retire (module 4) | `baseCell`, `isClopen_baseCell` (planned) |
| `d01cbef361ce` | 1502 | fixed size h, continuously enumerated clopen levels | theoremc-retire (module 4) | `level`, `pairwiseDisjoint_level`, `iUnion_level_eq` (planned) |
| `2a63696d979b` | 1502 | characteristic arrows between levels form a copy of M_h(k) | chain-matricial | `towerUnit_mul_towerUnit`, `isMatrixUnitFamily_towerUnit` (Algebra/CrossedProductTowerMatrixUnits, landed 5b3910136, queued for wiring) |
| `e55132ef58f5` | 1502 | the product contains the prescribed elements | chain-matricial | `isLocallyMatricialIn_transientIdeal` (module 5, planned) |

The key map rows for modules 2 and 4 name chain-matricial in `CHAIN_OWNERS`; main reassigned the modules to
theoremc-retire (chain-matricial.md, 09-13).  The census owner column should follow the reassignment.

## Truth audit of the printed claims (tex 1459–1514)

Hypotheses in force: X compact metrizable zero-dimensional, T a homeomorphism, Y = CR(T) closed and invariant.
Every printed claim of the range checks out as stated; no refutation.
- Extension of LC functions from closed Y: an LC function on Y is finite-valued with clopen fibers in Y, and a clopen
  subset of Y is the trace of a clopen subset of X.
- Kernel = compact support in U: the support of an LC function vanishing on Y is clopen, hence compact, and misses Y.
- Generation: `u^j d u^{-j} = 1_{T^j D}`, so `1_V = 1_V · 1_{T^j D}` lies in the ideal for clopen `V ⊆ T^j D`.
- Class size ≤ m: related points lie in one orbit inside C, and a wandering set meets an orbit at most once.
- Loop erasing ≤ m − 1: a shortest path visits distinct points of a class of size ≤ m.
- Unique arrow: U has no periodic points (Per(T) ⊆ CR(T)), so `T^n x = T^{n'} x` forces `n = n'`.
- Separating partition: each nonidentity partial shift σ is fixed-point free, so each x in its domain has a clopen V
  with `σ(V ∩ dom σ) ∩ V = ∅`; compactness and a common refinement give the partition.
- Clopen representative set: "a related point lies in an earlier atom" is a finite union of `σ⁻¹(atom)` tests.

## Findings for main

1. Producers of chain-matricial's residual interface Props (planned names; not yet stated on disk or origin), checked
   against the statements on origin 19d96c2c5 and the shared tree:
   - `DefectWanderingInterface T` (clopen `T(P) ⊆ P` ⇒ `P∖T(P)` wandering): PRODUCED on main by hull-euler's
     `GroupApproximation.Dynamics.isWandering_diff_image {T : Equiv.Perm X} (hP : T '' P ⊆ P) :
     IsWandering T (P \ T '' P)` (Dynamics/ChainRecurrence, root-imported).  Use `T.toEquiv`; clopenness is not needed.
   - `DefectCoverInterface T Y` for `Y = CR(T)`: produced IN FLIGHT by hull-euler's
     `compl_chainRecurrentSet_subset (T : X ≃ₜ X) : (chainRecurrentSet T)ᶜ ⊆ ⋃ P ∈ {P | IsClopen P ∧ T '' P ⊆ P},
     ⋃ n : ℤ, ⇑(T.toEquiv ^ n) '' (P \ T '' P)` and the endpoint `PrintedChainCoreCovering`
     (Dynamics/ChainRecurrenceCovering.lean, in hull-euler.files, unlanded).  It matches the interface at `Y = CR(T)`.
   - `DefectAvoidsCoreInterface T Y`: chain-core's `ClopenCrossedProduct.notMem_diff_image_of_mem` (on main, unwired)
     gives it only under `[Nontrivial k]` and `[IsDedekindFiniteMonoid (ClopenCrossedProduct (restrictHomeo T hY) k)]`,
     i.e. after R_Y is known directly finite (lem:chain-core-models plus S1 item 3).  At `Y = CR(T)` a direct
     dynamical proof exists and is short: `T(P)` and `P∖T(P)` are disjoint compact sets, so an ε-chain from
     `x ∈ P∖T(P)` with ε below the distances from `T(P)` to `X∖P` and to `P∖T(P)` stays in `T(P)` after the first step
     and never returns to `x`.  chain-matricial.md lists "wandering sets avoid CR(T)" as hull-euler's (S2).
2. Route note of chain-matricial (keys `1d0f9a56866c`, `fd026a61f84f`, `ff376e50f433`): Lean builds the exponent classes
   first and derives the separating partition, while the printed proof chooses the partition first.  COMMON_RULES
   rule 9 grades a different route `partial`; the owner states every printed claim is proved as stated.  The census
   grading of those three rows should check that each printed step has its own carrier.
3. Rows `549aa93e832f` and `bba38420cf8b` are `formalized` over ClopenDefectRestriction, which is landed but not yet
   root-reachable (wire queue).  They meet the root-closure rule only after that wave.
