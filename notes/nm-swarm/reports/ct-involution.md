# Lane ct-involution: lem:involution-localization (tex 1658–1694)

Lead: session nonsofic-existence-49 (ct-* lanes). Printed item: `non_mf_groups_exist.tex`, the paragraph
before the lemma (tex 1658–1661, the notation K_n(I)), `\label{lem:involution-localization}` (tex 1663–1670)
and its proof (tex 1672–1694). Added by 73a84cd9c.

## Printed statement

> Let $C$ be a full clopen section with bounded positive return times, put $p_C=1_C$ and $J=p_CIp_C$.
> Over any finite field, for every finite $F\subset I$ there is $w\in R_X^\times$ with $w-1\in I$, $w^2=1$,
> and $wFw^{-1}\subset J$. Over $\F_2$, every finite subset of $K_n(I)$ is simultaneously conjugate into the
> unitized $K_n(J)$ by $wI_n$; for $n\ge2$ this involution lies in $\EL_n(R_X)$.

## Route (as printed, with one construction-order note)

1. Finite support: F lies in `1_K R_X 1_K` for a clopen `K ⊆ X∖Y` covered by `m` wandering clopen sets
   (lem:chain-core-models defect cover, compactness).
2. Returns: every point of `K` has its first `2m` strictly future returns to `C` within `2mH`.
   At most `m` of them lie in `K` (wandering cover), so fresh section coordinates exist.
3. Matching and local constancy: each original coordinate is matched to a fresh coordinate in `C∖K`, constant
   on clopen cells. CONSTRUCTION ORDER: the printed proof reads the cells off the finite matrix-block construction
   of lem:transient-matrices (refined by K and C) and matches inside each class. Lean matches piece by piece: `K`
   is cut into `K_j ⊆ W_j`, and for `x ∈ K_j` the target is the first of its `2m` returns lying in `C∖K` and
   outside the targets of earlier pieces. At most `m` returns lie in `K` and at most `m−1` in earlier targets.
   The exponent is locally constant because `C`, `K` and the earlier targets are clopen. Every printed claim
   (2m returns, at least m fresh, matching, constancy on cells, swap, unitization) is proved; only the
   organisation of the cells differs.
4. Swap and unitization: `w = 1 − ∑ (1_{A_i} + 1_{T^{h_i}A_i}) + ∑ (u^{h_i}1_{A_i} + 1_{A_i}u^{−h_i})`, `w² = 1`,
   `w 1_K w⁻¹ = 1_{⊔ T^{h_i}A_i} ≤ p_C`, so `wFw⁻¹ ⊆ J`.
5. Kernel matrices: include the entries of deviations and inverse deviations in F; scalar conjugation.
   Over F_2, `wI_n ∈ K_n(I) ⊆ EL_n(R_X)` for `n ≥ 2` (the finite matrix argument of thm:core-mf-radical,
   chain-radical); local finiteness of `K_1(I)` (chain-radical).

## Modules

| module | content | status |
|---|---|---|
| `GroupApproximation/Dynamics/ClopenSwapInvolution.lean` | step 4: `IsSwapFamily`, `swapElement_mul_self`, `swapElement_mul_mul_swapElement`, `unit_zpow_mul_charFn`, `isSwapFamily_clopen`, `exists_swapUnit` | authored, probing |
| `GroupApproximation/Dynamics/ReturnPlacement.lean` | steps 2–3: counting of returns and visits, greedy placement | planned |
| `GroupApproximation/Dynamics/InvolutionLocalization.lean` | `PrintedInvolutionLocalization` and the assembly over piece Props | planned |

## Interfaces consumed

- landed: `ClopenCrossedProduct` (chain-core), `Dynamics.chainRecurrentSet`, `Dynamics.image_chainRecurrentSet`,
  `Dynamics.IsWandering`, `Dynamics.isWandering_diff_image` (hull-euler), `elementaryGroup` (Leavitt).
- not landed (named piece Props until the owners land): the defect cover of `X∖Y`
  (chain-itinerary `exists_defect_translate_of_not_mem_chainRecurrentSet`); over F_2, `K_n(I) ⊆ EL_n(R_X)` for
  `n ≥ 2` and local finiteness of `K_1(I)` (chain-radical module 3).

## Progress log

- 09-13 ~16:35: plan; ClopenSwapInvolution authored.
