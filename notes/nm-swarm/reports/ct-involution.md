# Lane ct-involution: lem:involution-localization (tex 1658–1694)

Lead: main (ct-* lanes). Printed item: `non_mf_groups_exist.tex`, the paragraph before the lemma
(tex 1658–1661, the notation K_n(I)), `\label{lem:involution-localization}` (tex 1663–1670) and its proof
(tex 1672–1694). Added by 73a84cd9c.

## Printed statement

> Let $C$ be a full clopen section with bounded positive return times, put $p_C=1_C$ and $J=p_CIp_C$.
> Over any finite field, for every finite $F\subset I$ there is $w\in R_X^\times$ with $w-1\in I$, $w^2=1$,
> and $wFw^{-1}\subset J$. Over $\F_2$, every finite subset of $K_n(I)$ is simultaneously conjugate into the
> unitized $K_n(J)$ by $wI_n$; for $n\ge2$ this involution lies in $\EL_n(R_X)$.

## Status

- **Finite-field clause CLOSED**: `ClopenCrossedProduct.involutionLocalizationRingClause_closed :
  InvolutionLocalizationRingClause`, `#audit_closed_axioms`, landed 0011a8b3a.
- F₂ clause: `involutionLocalizationMatrixClause_of_ringClause` (ms-core-3, probing) over
  `CoreKernelElementaryStatement` (ms-units, over chain-matricial's local matriciality of the transient ideal).

## Interface (landed 8b453b096; consumers: ct-rank-budget, ms-core-3, ms-units)

`GroupApproximation/Dynamics/InvolutionLocalizationStatement.lean`, namespace `GroupApproximation.ClopenCrossedProduct`:

| name | content |
|---|---|
| `coreTransientIdeal T k` | `transientIdeal T k (Dynamics.image_chainRecurrentSet T)`, the kernel of `R_X → R_Y` |
| `coreRestrictMatrixUnits T k n` | `Units.map (RingHom.mapMatrix (restrict T k _))`, defeq to ct-rank-budget's `glCoreRestrict` |
| `InvolutionLocalizationRingClause` | finite-field clause (tex 1664–1667) |
| `InvolutionLocalizationMatrixClause` | `F₂` clause (tex 1667–1669), including `w I_n ∈ EL_n` for `n ≥ 2` |
| `PrintedInvolutionLocalization` | `RingClause ∧ MatrixClause` |
| `ChainCoreDefectCoverStatement` | piece: `X ∖ Y` covered by translates of defects `P ∖ T(P)`; CLOSED `chainCoreDefectCoverStatement_holds` (0011a8b3a) |
| `CoreKernelElementaryStatement` | piece: over `F₂`, `n ≥ 2`, `ker (coreRestrictMatrixUnits T (ZMod 2) n) ≤ EL_n(R_X)` |

## Route (as printed, with one construction-order note)

1. Finite support (tex 1673): `exists_clopen_support`. F lies in `1_K R_X 1_K` for a clopen `K ⊆ X∖Y`.
2. Wandering cover (tex 1673–1674): `exists_wandering_clopen_cover`, from `ChainCoreDefectCoverStatement` and
   `Dynamics.isWandering_diff_image`. Bounded returns: `exists_uniform_return`.
3. Returns and matching (tex 1675–1686): `Dynamics.card_returns_ge` (2m returns within 2mL),
   `Dynamics.card_visits_le` (at most m in K), `Dynamics.exists_returnPlacement`.
   CONSTRUCTION ORDER: the printed proof reads the cells off the matrix-block construction of
   lem:transient-matrices and matches inside each class. Lean matches piece by piece: K is cut into
   `K ∩ W_j ∖ ⋃_{i<j} W_i`, and a point of the j-th piece goes to the first of its first 2m returns lying in
   `C∖K` and outside the targets of earlier pieces (at most m returns in K, at most j < m in earlier targets).
   Every printed claim is proved; only the organisation of the cells differs.
4. Swap and unitization (tex 1684–1687): `exists_swapUnit`, with `w⁻¹ = w` and `w 1_A w⁻¹ = 1_{T^h A}` on each
   cell; `w 1_K w⁻¹ = ∑ 1_{T^h A} ≤ p_C`, so `w F w⁻¹ ⊆ J` (`conj_eq_sandwich`, `sandwich_eq_self`).
5. Kernel matrices (tex 1689–1693): ms-core-3 (see Splits).

## Modules

| module | content | status |
|---|---|---|
| `Dynamics/ClopenSwapInvolution.lean` | step 4: `IsSwapFamily`, `swapElement_mul_self`, `swapElement_mul_mul_swapElement`, `unit_zpow_mul_charFn`, `isSwapFamily_clopen`, `exists_swapUnit` | LANDED 3bd81b1ad, wire-queued |
| `Dynamics/ReturnPlacement.lean` | step 3: `card_returns_ge`, `card_visits_le`, `card_target_visits_le`, `IsPlacement`, `exists_returnPlacement` | LANDED bc6aa7b90, wire-queued |
| `Dynamics/InvolutionLocalizationStatement.lean` | the interface above | LANDED 8b453b096, wire-queued |
| `Dynamics/TransientSupport.lean` | steps 1–2: `CoeffVanishOn` (ideal closure), `exists_clopen_support`, `exists_wandering_clopen_cover`, `exists_uniform_return` | LANDED 8b453b096, wire-queued |
| `Dynamics/InvolutionLocalizationRing.lean` | `involutionLocalizationRingClause_of_cover`; `zpow_mem_chainRecurrentSet`, `mem_coreTransientIdeal_iff`, `charFn_eq_sum_of_partition`, `conj_eq_sandwich`, `sandwich_eq_self` | LANDED cc4d23eff, wire-queued |
| `Dynamics/InvolutionLocalizationRingClosed.lean` | `chainCoreDefectCoverStatement_holds`, `involutionLocalizationRingClause_closed` (closed endpoints) | LANDED 0011a8b3a, wire-queued |

## Splits (agreed directly with the helpers main sent)

- ms-core-3: `involutionLocalizationMatrixClause_of_ringClause (hring : InvolutionLocalizationRingClause)
  (hel : CoreKernelElementaryStatement) : InvolutionLocalizationMatrixClause`, in `Dynamics/InvolutionLocalizationMatrix.lean`.
- ms-units: a producer of `CoreKernelElementaryStatement` over `TransientIdealLocallyMatricialFTwoStatement` (with
  chain-radical's landed `ker_elementaryMatrixUnitMap_le_elementaryGroup`), and ct-rank-budget's
  `UnitKernelLocallyFiniteStatement` (tex 1693, K_1(I) locally finite), in `Dynamics/CoreKernelFTwo.lean`.

## Residual statements

- `CoreKernelElementaryStatement` := `∀ X [MetricSpace X] [CompactSpace X] [TotallyDisconnectedSpace X] [Nonempty X]
  T n, 2 ≤ n → (coreRestrictMatrixUnits T (ZMod 2) n).ker ≤ elementaryGroup (Fin n) (ClopenCrossedProduct T (ZMod 2))`
  (ms-units, over chain-matricial's local matriciality of the transient ideal).
- The matrix clause assembly (ms-core-3, probing).

## Progress log

- 09-13 ~16:35: plan; ClopenSwapInvolution authored.
- 09-13 16:55: ClopenSwapInvolution landed. 17:10: ReturnPlacement landed.
- 09-13 17:37: statement (kernel spelling) and TransientSupport landed; splits with ms-core-3 and ms-units agreed.
- 09-13 17:47: ring clause assembly landed. 17:51: finite-field clause closed (0011a8b3a).
