# Lane ct-involution: lem:involution-localization (tex 1658–1694); cells of lem:transient-matrices

Lead: main (ct-* lanes). Item 1: `non_mf_groups_exist.tex`, the paragraph before the lemma (tex 1658–1661, the
notation K_n(I)), `\label{lem:involution-localization}` (tex 1663–1670) and its proof (tex 1672–1694), added by
73a84cd9c. Item 2 (main, 09-13 ~18:20): a piece of `TransientIdealLocallyMatricialFTwoStatement`, the single residual
of item 1.

## Item 1: lem:involution-localization

> Let $C$ be a full clopen section with bounded positive return times, put $p_C=1_C$ and $J=p_CIp_C$.
> Over any finite field, for every finite $F\subset I$ there is $w\in R_X^\times$ with $w-1\in I$, $w^2=1$,
> and $wFw^{-1}\subset J$. Over $\F_2$, every finite subset of $K_n(I)$ is simultaneously conjugate into the
> unitized $K_n(J)$ by $wI_n$; for $n\ge2$ this involution lies in $\EL_n(R_X)$.

Status:
- **Finite-field clause CLOSED**: `ClopenCrossedProduct.involutionLocalizationRingClause_closed :
  InvolutionLocalizationRingClause`, `#audit_closed_axioms`, landed 0011a8b3a.
- **Printed lemma composed** (b30db7cd0): `ClopenCrossedProduct.printedInvolutionLocalization_of_matricial
  (h : TransientIdealLocallyMatricialFTwoStatement) : PrintedInvolutionLocalization`, and
  `printedInvolutionLocalization_of_coreKernelElementary (hel : CoreKernelElementaryStatement)`.
- Residual: `TransientIdealLocallyMatricialFTwoStatement` (CoreKernelFTwo:74). See item 2.

Interface (landed 8b453b096; consumers: ct-rank-budget, ms-core-3, ms-units),
`GroupApproximation/Dynamics/InvolutionLocalizationStatement.lean`, namespace `GroupApproximation.ClopenCrossedProduct`:

| name | content |
|---|---|
| `coreTransientIdeal T k` | `transientIdeal T k (Dynamics.image_chainRecurrentSet T)`, the kernel of `R_X → R_Y` |
| `coreRestrictMatrixUnits T k n` | `Units.map (RingHom.mapMatrix (restrict T k _))`, defeq to ct-rank-budget's `glCoreRestrict` |
| `InvolutionLocalizationRingClause` | finite-field clause (tex 1664–1667) |
| `InvolutionLocalizationMatrixClause` | `F₂` clause (tex 1667–1669), including `w I_n ∈ EL_n` for `n ≥ 2` |
| `PrintedInvolutionLocalization` | `RingClause ∧ MatrixClause` |
| `ChainCoreDefectCoverStatement` | piece: `X ∖ Y` covered by translates of defects; CLOSED `chainCoreDefectCoverStatement_holds` (0011a8b3a) |
| `CoreKernelElementaryStatement` | piece: over `F₂`, `n ≥ 2`, `ker (coreRestrictMatrixUnits T (ZMod 2) n) ≤ EL_n(R_X)`; `coreKernelElementaryStatement_of_matricial` (ms-units, eaa87e3a1) |

Route (as printed, with one construction-order note):
1. Finite support (tex 1673): `exists_clopen_support`.
2. Wandering cover (tex 1673–1674): `exists_wandering_clopen_cover`; bounded returns `exists_uniform_return`.
3. Returns and matching (tex 1675–1686): `Dynamics.card_returns_ge`, `Dynamics.card_visits_le`,
   `Dynamics.exists_returnPlacement`. CONSTRUCTION ORDER: the printed proof reads the cells off the matrix-block
   construction of lem:transient-matrices and matches inside each class; Lean matches piece by piece over the wandering
   cover. Census rows `07ab0fbe6cfc`, `3468c60b2946`, `6baf73489057` are partial for this reason.
4. Swap and unitization (tex 1684–1687): `exists_swapUnit`; `conj_eq_sandwich`, `sandwich_eq_self`.
5. Kernel matrices (tex 1689–1693): `involutionLocalizationMatrixClause_of_ringClause` (ms-core-3, e131463f7).

Modules:

| module | content | status |
|---|---|---|
| `Dynamics/ClopenSwapInvolution.lean` | `IsSwapFamily`, `exists_swapUnit` | LANDED 3bd81b1ad, wire-queued |
| `Dynamics/ReturnPlacement.lean` | `card_returns_ge`, `card_visits_le`, `exists_returnPlacement` | LANDED bc6aa7b90, wire-queued |
| `Dynamics/InvolutionLocalizationStatement.lean` | the interface above | LANDED 8b453b096, wire-queued |
| `Dynamics/TransientSupport.lean` | `CoeffVanishOn`, `exists_clopen_support`, `exists_wandering_clopen_cover`, `exists_uniform_return` | LANDED 8b453b096, wire-queued |
| `Dynamics/InvolutionLocalizationRing.lean` | `involutionLocalizationRingClause_of_cover` and helpers | LANDED cc4d23eff, wire-queued |
| `Dynamics/InvolutionLocalizationRingClosed.lean` | `chainCoreDefectCoverStatement_holds`, `involutionLocalizationRingClause_closed` | LANDED 0011a8b3a, wire-queued |
| `Dynamics/InvolutionLocalizationClosed.lean` | `printedInvolutionLocalization_of_coreKernelElementary`, `printedInvolutionLocalization_of_matricial` | LANDED b30db7cd0, wire-queued |

Census rows: `metadata/nm-census-rows/ct-involution.tsv` (14 keys, 99271dd69); `50c5dd41dff4`, `5c06eec5555b`,
`1c114e2c4209` are ms-core-3's.

## Item 2: cells of lem:transient-matrices (for `TransientIdealLocallyMatricialFTwoStatement`)

Split agreed directly with ms-units (09-13 ~18:28):
- ct-involution: the CELLS only, `GroupApproximation/Dynamics/TransientCells.lean`.
- ms-units: `Dynamics/TransientClassSaturation` (landed 80ae3fb5b), `Dynamics/TransientTowerFamily` (matrix unit family over
  given cells), `Dynamics/TransientTowerExpansion` (`exists_matrix_eq_sum_transientTower`, the expansion), and the assembly
  of `TransientIdealLocallyMatricialFTwoStatement` and ms-compress-3's `ChainCore.TransientIdealLocallyMatricialStatement`.

CLAIM: `ClopenCrossedProduct.exists_transientCells (hcover : ChainCoreDefectCoverStatement) (X : Type) [MetricSpace X]
[CompactSpace X] [TotallyDisconnectedSpace X] (T : X ≃ₜ X) (k : Type) [Ring k] (F : Finset (ClopenCrossedProduct T k))
(hF : ∀ x ∈ F, x ∈ transientIdeal T k (Dynamics.image_chainRecurrentSet T))`, giving `C` clopen off `CR(T)`, `E`, `m` with
`ExponentBound T C m`, cells `cell : Fin M → Set X` with `S`, `hcell`, `rep`, inside representative cells, pairwise disjoint,
covering `baseSet`, the coefficient support clause and the constancy clause (verbatim the `hx`/`hconst` binders of ms-units'
expansion). Route: `exists_clopen_support`, `exists_wandering_clopen_cover`, `exponentBound_of_wanderingCover`, and
`exists_cells`: nonempty fibres in `baseSet` of `y ↦ (class of y, coefficient values of F at all class levels)`, finite by
`IsLocallyConstant.range_finite`. Status: probing.

## Progress log

- 09-13 ~16:35: plan; ClopenSwapInvolution authored.
- 09-13 16:55: ClopenSwapInvolution landed. 17:10: ReturnPlacement landed.
- 09-13 17:37: statement (kernel spelling) and TransientSupport landed; splits with ms-core-3 and ms-units agreed.
- 09-13 17:47: ring clause assembly landed. 17:51: finite-field clause closed (0011a8b3a).
- 09-13 18:00: census rows landed fdd12f7d7; three F₂ rows handed to ms-core-3 at ad266b720.
- 09-13 18:17: printed lemma composed over TransientIdealLocallyMatricialFTwoStatement (b30db7cd0).
- 09-13 ~18:28: item 2, cells split agreed with ms-units; TransientCells authored and probing.
