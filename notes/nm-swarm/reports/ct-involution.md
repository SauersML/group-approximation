# Lane ct-involution: lem:involution-localization (tex 1658–1694); cells of lem:transient-matrices

Lead: main (ct-* lanes). Item 1: `non_mf_groups_exist.tex`, the paragraph before the lemma (tex 1658–1661, the
notation K_n(I)), `\label{lem:involution-localization}` (tex 1663–1670) and its proof (tex 1672–1694), added by
73a84cd9c. Item 2 (main, 09-13 ~18:20): a piece of `TransientIdealLocallyMatricialFTwoStatement`, the single residual
of item 1.

## Status: both items CLOSED (49663bacb)

Closed endpoints in `GroupApproximation/Dynamics/TransientCellsClosed.lean` (`#audit_closed_axioms`, wire-queued):
- `ClopenCrossedProduct.printedInvolutionLocalization_closed : PrintedInvolutionLocalization` (tex 1663–1694);
- `transientIdealLocallyMatricialStatement_holds : ChainCore.TransientIdealLocallyMatricialStatement` (lem:transient-matrices,
  locally matricial clause, every finite field);
- `transientIdealLocallyMatricialFTwoStatement_holds`, `coreKernelElementaryStatement_holds`,
  `unitKernelLocallyFiniteStatement_holds`, `transientCellsStatement_holds`.

## Item 1: lem:involution-localization

> Let $C$ be a full clopen section with bounded positive return times, put $p_C=1_C$ and $J=p_CIp_C$.
> Over any finite field, for every finite $F\subset I$ there is $w\in R_X^\times$ with $w-1\in I$, $w^2=1$,
> and $wFw^{-1}\subset J$. Over $\F_2$, every finite subset of $K_n(I)$ is simultaneously conjugate into the
> unitized $K_n(J)$ by $wI_n$; for $n\ge2$ this involution lies in $\EL_n(R_X)$.

Interface (landed 8b453b096), `GroupApproximation/Dynamics/InvolutionLocalizationStatement.lean`, namespace
`GroupApproximation.ClopenCrossedProduct`:

| name | content |
|---|---|
| `coreTransientIdeal T k` | `transientIdeal T k (Dynamics.image_chainRecurrentSet T)`, the kernel of `R_X → R_Y` |
| `coreRestrictMatrixUnits T k n` | `Units.map (RingHom.mapMatrix (restrict T k _))`, defeq to ct-rank-budget's `glCoreRestrict` |
| `InvolutionLocalizationRingClause` | finite-field clause (tex 1664–1667); CLOSED `involutionLocalizationRingClause_closed` (0011a8b3a) |
| `InvolutionLocalizationMatrixClause` | `F₂` clause (tex 1667–1669); `involutionLocalizationMatrixClause_of_ringClause` (ms-core-3, e131463f7) |
| `PrintedInvolutionLocalization` | `RingClause ∧ MatrixClause`; CLOSED `printedInvolutionLocalization_closed` (49663bacb) |
| `ChainCoreDefectCoverStatement` | CLOSED `chainCoreDefectCoverStatement_holds` (0011a8b3a) |
| `CoreKernelElementaryStatement` | CLOSED `coreKernelElementaryStatement_holds` (49663bacb) |

Route (as printed, with one construction-order note):
1. Finite support (tex 1673): `exists_clopen_support`.
2. Wandering cover (tex 1673–1674): `exists_wandering_clopen_cover`; bounded returns `exists_uniform_return`.
3. Returns and matching (tex 1675–1686): `Dynamics.card_returns_ge`, `Dynamics.card_visits_le`,
   `Dynamics.exists_returnPlacement`. CONSTRUCTION ORDER: the printed proof reads the cells off the matrix-block
   construction of lem:transient-matrices and matches inside each class; Lean matches piece by piece over the wandering
   cover. Census rows `07ab0fbe6cfc`, `3468c60b2946`, `6baf73489057` are partial for this reason.
4. Swap and unitization (tex 1684–1687): `exists_swapUnit`; `conj_eq_sandwich`, `sandwich_eq_self`.
5. Kernel matrices (tex 1689–1693): ms-core-3's matrix clause over `coreKernelElementaryStatement_holds`.

## Item 2: cells of lem:transient-matrices

Split agreed directly with ms-units (09-13 ~18:28): ct-involution the cells; ms-units the class saturation (80ae3fb5b),
the tower family, the expansion and the assembly (`TransientIdealLocallyMatricial`, 963111df2).

`ClopenCrossedProduct.exists_transientCells (hcover : ChainCoreDefectCoverStatement) X T k F hF` (TransientCells,
0ec08fc2c): a clopen `C` off `CR(T)` containing the coefficient supports of `F` (`mem_of_charFn_mul_eq_self`,
`zpow_mem_of_mul_charFn_eq_self`), the exponents `E`, `ExponentBound T C m` from the wandering cover, and cells from
`exists_cells`: the nonempty fibres in `baseSet` of `y ↦ (class of y, coefficient values of F at all class levels)`, finite by
`IsLocallyConstant.range_finite`. Construction note: the representative is the point of least exponent (`baseSet`) rather
than the first occupied atom of a separating partition.

## Modules

| module | content | status |
|---|---|---|
| `Dynamics/ClopenSwapInvolution.lean` | `IsSwapFamily`, `exists_swapUnit` | LANDED 3bd81b1ad, wire-queued |
| `Dynamics/ReturnPlacement.lean` | `card_returns_ge`, `card_visits_le`, `exists_returnPlacement` | LANDED bc6aa7b90, wire-queued |
| `Dynamics/InvolutionLocalizationStatement.lean` | the interface above | LANDED 8b453b096, wire-queued |
| `Dynamics/TransientSupport.lean` | `CoeffVanishOn`, `exists_clopen_support`, `exists_wandering_clopen_cover`, `exists_uniform_return` | LANDED 8b453b096, wire-queued |
| `Dynamics/InvolutionLocalizationRing.lean` | `involutionLocalizationRingClause_of_cover` and helpers | LANDED cc4d23eff, wire-queued |
| `Dynamics/InvolutionLocalizationRingClosed.lean` | `chainCoreDefectCoverStatement_holds`, `involutionLocalizationRingClause_closed` | LANDED 0011a8b3a, wire-queued |
| `Dynamics/InvolutionLocalizationClosed.lean` | `printedInvolutionLocalization_of_coreKernelElementary`, `printedInvolutionLocalization_of_matricial` | LANDED b30db7cd0, wire-queued |
| `Dynamics/TransientCells.lean` | `isLocallyConstant_pi`, `exists_finset_classExponents`, `exists_cells`, `exists_transientCells` | LANDED 0ec08fc2c, wire-queued |
| `Dynamics/TransientCellsClosed.lean` | the six closed endpoints above | LANDED 49663bacb, wire-queued |

Census rows: `metadata/nm-census-rows/ct-involution.tsv` (14 keys); `b13eccd8f0ec` graded formalized after 49663bacb;
`50c5dd41dff4`, `5c06eec5555b`, `1c114e2c4209` are ms-core-3's.

## Build trap (from ms-core-3)

The chain-core statement modules do not import `Mathlib.Algebra.Field.ZMod`. Specializing a `∀ k [Field k]` statement at
`ZMod 2` without it makes the unifier unfold `ZMod 2` arithmetic and time out. Import it and add
`haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩`.

## Progress log

- 09-13 ~16:35: plan; ClopenSwapInvolution authored.
- 09-13 16:55: ClopenSwapInvolution landed. 17:10: ReturnPlacement landed.
- 09-13 17:37: statement (kernel spelling) and TransientSupport landed; splits with ms-core-3 and ms-units agreed.
- 09-13 17:47: ring clause assembly landed. 17:51: finite-field clause closed (0011a8b3a).
- 09-13 18:00: census rows landed fdd12f7d7; three F₂ rows handed to ms-core-3 at ad266b720.
- 09-13 18:17: printed lemma composed over TransientIdealLocallyMatricialFTwoStatement (b30db7cd0).
- 09-13 ~18:28: item 2, cells split agreed with ms-units.
- 09-13 18:38: TransientCells landed (0ec08fc2c). 18:42: both items closed (49663bacb).
