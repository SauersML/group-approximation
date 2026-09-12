# Lane `lix-evenside-n` — Step D at rank `n` mod every prime dividing the rank, rank-`n` Step A, and the glue of Lemma 2

Successor of `sp-evenside-n` (report `notes/lix-stronger-lane-reports/sp-evenside-n.md`, read in
full).  Owns `GroupApproximation/CharClass/LIXStepDGen*.lean` and, by the lead's ruling of
2026-09-11 ~21:55, `CharClass/LIXLemmaTwoGen*` (rank-`n` Step A, `StepCHalf`, the glue, the
coordinate-swap bridge).  Clone: SHARED `lix-c` (rule 20).

## STEP 0 (2026-09-11 ~21:25)

* The predecessor's `LIXStepDGenParity`, `LIXStepDGenData`, `LIXStepDGenAxiomCheck` are on origin/main
  (batch 1, f643c96ea) byte-identical to the shared tree; nothing of this lane was unlanded.
* Scope (1), the `F₂` bridge `Gen.WuStepDData` / `Gen.stepD_of_wu(_stage)` with the `n = 2` rfl
  bridges, was already DONE and compiled.

## GREEN

* Probe `0911-215333-54272` on lix-c (acn112, 8818 jobs, PROBE GREEN): `BUILT` + `COMPILED`
  `CharClass.LIXStepDGenModP`, `CharClass.LIXStepDGenHalf`; `#audit_axioms` classical.
* Probe `0911-221342-93884` on lix-c (SLURM acn75, 8827 jobs, PROBE GREEN, first try): `BUILT` +
  `COMPILED` `CharClass.LIXLemmaTwoGenStepA`, `CharClass.LIXLemmaTwoGenGlue`; `#audit_axioms` classical.

## LANDED

* 1aaaa40d6 (unverified), e644de5e0 / 36226d62e (attic) — superseded by:
* **8b8f85baf NORMAL** — `LIXStepDGenModP`, `LIXStepDGenHalf` from the green record above.
  WIRE top: `GroupApproximation.CharClass.LIXStepDGenHalf`.
* 93e1d2992 — `LIXLemmaTwoGenStepA`, `LIXLemmaTwoGenGlue`, landed unverified; the green record of
  probe 0911-221342-93884 matches those origin bytes (md5 8d0433d2…, 2fea7e83…), so both are COMPILED
  on main with no second commit.  WIRE top: `GroupApproximation.CharClass.LIXLemmaTwoGenGlue`
  (reaches StepA, LIXStepDGenHalf, LIXStepDGenModP).

## What is proved (declarations)

`LIXStepDGenModP`: `Gen.gamma_rank_eq_zero_modP` (uniform theorem at `m + (n + 1)`, index-orientation
fix); `Gen.ModPStepDData n p dd R H γ`; `Gen.ModPStepDData.toParityPData` (INSTANCE of lix-evenside's
`ParityPData`, three fields derived by their producers, nothing re-derived);
`Gen.ModPStepDData.gamma_top_eq_zero`.

`LIXStepDGenHalf`: `Gen.StepDHalf n dd topClass` (section-free); `stepDHalf_of_wu(_stage)`,
`stepDHalf_of_modP(_stage)`, `stepDHalf_powers_of_modP / _of_wu` (∀ k, p ∤ k → ∀ j), and
`stepDHalf_two_iff` (n = 2 `Iff.rfl` against `LemmaTwoInput`'s stepD conjunct).

`LIXLemmaTwoGenStepA` (compiled): `Gen.fromBlocks_rankOneProj_zero`, `Gen.isStarProjection_FHmatOf`,
`Gen.isStarProjection_EHmat`, `Gen.exists_cornerUnitary_of_continuousMvNEquiv` (for any continuous unit
`b`: `G (e_last, 0) = (b, 0)`), `Gen.hasStepAUnitary_of_continuousMvNEquiv`,
`hasStepAUnitary_of_continuousMvNEquiv_of_gen` (rank-two bridge).

`LIXLemmaTwoGenGlue` (compiled): `Gen.lastZeroSwap`, `Gen.isCornerUnitary_submatrix_lastZeroSwap`,
`Gen.submatrix_lastZeroSwap_mulVec_eZero`; **`Gen.StepCHalf`** (committed spelling, sent to the lead);
**`Gen.lemmaTwoFor_of_halves`**; `Gen.lemmaTwoFor_powers_of_halves`; `Gen.lemmaTwoFor_powers_of_stepC_modP`.

## The section bridge (ruling b)

`LemmaTwoFor` keeps `e_last`, KGen keeps `e₀`.  Bridged by right multiplication, not conjugation of the
complements: Step A gives `G (e_last, 0) = (b, 0)`; `G ∘ τ = (G m).submatrix id τ` with `τ` the swap
`0 ↔ last` (identity on `H`) is a continuous corner unitary (τ fixes `V`) carrying `(e₀, 0)` to `(b, 0)`.
So Step C at `e₀` is consumed for the SAME section `b = KGen.bVecK n (k − 1)`; no `σ ∘ b` anywhere.

## Concrete mod-p assembly at the real mapping torus (option (a), approved 2026-09-11 ~22:50)

`H` and `R` of `ParityPData` must be COMMUTATIVE; over `K` at odd `p` the whole ring `TotalHOf K X` is only
graded-commutative, so they are the EVEN parts.  `CharClass/LIXStepDGenRealEven.lean`: `Gen.evenPart K X`
(subring of classes vanishing in odd degrees), `Gen.instCommRingEvenPart` (commutative with no hypothesis,
from lix-cupone's `TotalHOf.mul_comm_of_isEven_left`), `Gen.evenMap K f` (pullback as a ring hom),
`Gen.evenRestrictAdd f hf` (P^i restricted).  `CharClass/LIXStepDGenReal.lean`: `Gen.tClassOf`, `Gen.xClassOf`,
`Gen.zClass`, `Gen.isEven_zClass`, `Gen.zClass_mul_self` (z² = 0 with NO sign: z even ⇒ z t = t z, so
z z = (t t) x x = 0 from H²(S¹) = 0 alone), `Gen.RealTorusModP` (torus inputs: H²(S¹)=0, Künneth z_inj, P^i
on N and Y with P⁰ = id, Cartan, naturality, P^{>0} t = P^{>0} x = 0, instability on Y),
`Gen.RealTorusModP.PN_zClass` (P(z) = z by Cartan), `Gen.RealBundleModP` (bundle inputs: even Chern classes,
Künneth components, degree of b, slice, Wu with unit c), `RealBundleModP.instability_b`,
**`RealBundleModP.toModPStepDData`** (the instance over the even parts), `RealBundleModP.gamma_top_eq_zero`,
`Gen.realWu_of_splitting` (field wu from lix-evenside's `wu_field_of_splitting`; unit via
`ParityP.isUnit_wuLeading`), `Gen.stepDHalf_of_realModP`, `Gen.lemmaTwoFor_powers_of_stepC_realModP`.
Landed unverified: d6009101a + 938aa5bb4 (RealEven), 73ff46a09 + b4d828247 (Real).  **COMPILED**: probe
0911-233331-59048 on lix-c (acn112, 8849 jobs, PROBE GREEN, BUILT + COMPILED both; md5 910ff65d…, b52eb348… = origin
bytes).  WIRE top: `GroupApproximation.CharClass.LIXStepDGenReal` (reaches RealEven, LIXLemmaTwoGenGlue).

## Torus fields discharged, and the p = 2 composition (2026-09-12 ~00:10)

COMPILED in probe 0912-000930-45207 (lix-c, acn112, 9310 jobs, PROBE GREEN, BUILT + COMPILED all three; md5 = origin
bytes): `CharClass/LIXStepDGenRealTorus` (485a00387): `Gen.componentOf_map`, `Gen.componentOf_of_mul` (components over K),
**`Gen.z_inj_of_degreewise`** (the field `z_inj` from the right-nested cast-free degreewise statement; K form of
`Gen.tx_inj_of_degreewise`), **`Gen.circle_two_sphereOf`** (H²(S¹;K) = 0 from lix-cupone's `sphere_coh_eq_zero_of_neOf`),
`Gen.one_ne_zero_of_nonempty` (unit class pulls back to a point), **`Gen.charP_evenPart`, `Gen.expChar_evenPart`**
(`ExpChar (evenPart (ZMod p) Y) p` for `[Fact p.Prime] [Nonempty Y]`).  `CharClass/LIXStepDGenRealTorusModel` (0d189d933):
**`Gen.z_inj_torusOf`** (on lix-coeff's model `KnTwo.torusBaseOf Y n = (Y × S^{2n+1}) × S¹`, any nonzero sphere classes,
through `KnTwo.tx_inj_degree_of_ne_zeroOf`), `Gen.circle_two_torusOf`.  `CharClass/LIXLemmaTwoGenTwo` (0d189d933):
**`Gen.lemmaTwoFor_powers_two_lixChernOf`** — for even n ≥ 2, every odd k, every stage j,
`LemmaTwoFor n (lixDD n j) (KGen.bVecK n (k − 1))`, with ONE class on both halves
(`KGen.lixChernOf n (KGen.lixChern n (lixDD n j))` at N := `KGen.lixN n (lixDD n j)`), from lix-oddside-n's
`KGen.KZeroLocalData` and the mod-2 `Gen.WuStepDData` at `lixN`.
Remaining torus fields: the reduced powers only (lix-steenrod).  A trap: `refine DirectSum.ext fun c => ?_` on
`TotalHOf` leaves `(i : ?) → AddCommMonoid ?` stuck; use `ext c` (probe 0911-235748-53450).

## STOPPED 2026-09-12 (lead's stop ruling, `LIX_LANES.md` "STOPPED"): residual (b) of the p = 2 composition

The lead's target was the binder `data` of `Gen.lemmaTwoFor_powers_two_lixChernOf` (`CharClass/LIXLemmaTwoGenTwo`):

```lean
(data : ∀ j G, Continuous G → (∀ m, IsCornerUnitary (Vmat n m) (G m)) →
  WuStepDData n (LIX.Gen.lixDD n j) (pY j) (q₁ j) (qodd j) (σ₁ j) (σodd j)
    (KGen.lixChernOf n (KGen.lixChern n (LIX.Gen.lixDD n j))
      (mappingTorus (Vmat n) G circHoriz circHeight)))
```

The lead split the work: `sq_b`, `split`, `slice` and `hC` belong to this lane, and `tx_inj`, `gamma_eq`, `hS₁`/`hSodd` and the projections belong to lix-coeff.

**Green.** No new green this session. Every earlier module is still COMPILED with origin bytes: `LIXStepDGenModP`, `LIXStepDGenHalf`, `LIXLemmaTwoGenStepA`, `LIXLemmaTwoGenGlue`, `LIXStepDGenRealEven`, `LIXStepDGenReal`, `LIXStepDGenRealTorus`, `LIXStepDGenRealTorusModel`, `LIXLemmaTwoGenTwo`. The shared-tree copies match the green record `0912-000930-45207`, so nothing of this lane is in flight.

**Landed unverified: 84b833ac2.** `CharClass/LIXStepDGenSplit.lean` (not compiled, not wired):

```lean
theorem Gen.hasSplitting_lixN (n : ℕ) (G : baseM n dd → Matrix (VIdx n dd) (VIdx n dd) ℂ)
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat n m) (G m)) :
    Wu.HasSplitting (KGen.lixN n dd)
      (KGen.lixChernOf n (KGen.lixChern n dd) (mappingTorus (Vmat n) G circHoriz circHeight))
```

This is the rank-two `Wu.hasSplitting_lix` proof over `KGen.lixN n dd` with the KGen API: `KGen.lixChernOf_mappingTorus`, `KGen.lixChern_mappingTorus`, `KGen.one_le_lixRank`, `KGen.rank_lixBundle`, `Wu.hasSplitting_flag`, `Wu.hasSplitting_of_component`. It is the field `split`.

**Closed by existing declarations.** `hC : Wu.CartanTotal` is `Wu.cartanTotal` (ParityEvenTransport).

**lix-coeff's announced objects** (message of 2026-09-12, module `CharClass/CohomologyKunnethLixN.lean`, namespace `KnLix`; this lane has not checked them against origin):
* `Y := TopCat.of (baseY dd)`, `S₁ := TopCat.of (Sphere 1)`, `Sodd := TopCat.of (Sphere (2 * n + 1))`.
* `KnLix.lixIso n dd : KGen.lixN n dd ≅ TopCat.of (KnTwo.torusBaseOf (baseY dd) n)`.
* `pY := KnLix.prY n dd`, `q₁ := KnLix.prS1 n dd`, `qodd := KnLix.prSodd n dd`, each `(lixIso n dd).hom ≫ KnTwo.pr*Of`.
* `σ₁ := sphereTopClass 1 _`, `σodd := sphereTopClass (2 * n + 1) _`.
* `hS₁`/`hSodd` from `hasSphereCohomology_sphere`.
* Field `tx_inj` is `KnLix.tx_inj n dd`.
* `KnLix.chern_split_mappingTorus n dd hGc hGu k : ∃ α β, (2 * k < 2 * n + 2 → β = 0) ∧ KGen.lixChernOf n (KGen.lixChern n dd) (mappingTorus (Gen.Vmat n) G circHoriz circHeight) k = TotalH.map pY (TotalH.of _ (2 * k) α) + Wu.tClass q₁ σ₁ * Gen.sphereClass qodd σodd * TotalH.map pY (TotalH.of _ (2 * k - (2 * n + 2)) β)`.

**Unfinished (exact field statements at `N := KGen.lixN n dd`, `γ := KGen.lixChernOf n (KGen.lixChern n dd) (mappingTorus (Vmat n) G circHoriz circHeight)`):**
* `gamma_eq : ∀ k : ℕ, γ k = TotalH.map pY (a k) + Wu.tClass q₁ σ₁ * sphereClass qodd σodd * TotalH.map pY (b k)`
  * Obtained by `choose` on `KnLix.chern_split_mappingTorus`, with `a k := TotalH.of Y (2 * k) (α k)` and `b k := TotalH.of Y (2 * k - (2 * n + 2)) (β k)`.
  * The planned wrapper `Gen.ChernSplitN` (alpha, beta, beta_low, split) and `Gen.WuStepDData.ofChernSplitN` in `CharClass/LIXStepDGenChernSplit.lean` were NOT written.
* `sq_b : ∀ k j : ℕ, 2 * k < j + (2 * n + 2) → Steenrod.SqH Y j (b k) = 0`
  * Route: `Gen.sq_b_of_grading n b hlow hdeg`.
  * `hlow k` comes from `β k = 0` when `2 * k < 2 * n + 2`.
  * `hdeg k c hc` is `⟨cohCast (show 2 * k - (2 * n + 2) = c by omega) (β k), (totalH_of_cohCast _ _).symm⟩`.
  * Template: `KnTwo.hgamma_and_hsq_b` (CohomologyParityKunneth), with 6 replaced by 2n+2.
  * NOT written.
* `slice : ∀ q : ℕ, a q = (sliceClass Finset.univ gen dd).coeff q`
  * NOT written. Planned file `CharClass/LIXStepDGenSlice.lean`.
  * Route, step 1: take a section `s : Y ⟶ N` of `pY` at a constant circle coordinate. Then `TotalH.map s (Wu.tClass q₁ σ₁) = 0` by `pull_const_eq_zero`, which gives `a q = TotalH.map s (γ q)`, following `KnTwo.alpha_eq_pull_nSlice`.
  * Route, step 2: naturality along a rank-`n` `lixSliceMapN n dd p1 u : C(baseY dd, ↥sphereOne × Gen.baseM n dd)` via `LH.chern_comap`, following `pull_lixChern_lixSlice`.
  * Remaining leaf: the rank-`n` slice value `∀ q, TotalH.of Y (2 * q) (LH.chernOf (comap (lixSliceMapN n dd p1 u) ⟨P, hcont, hproj⟩) (lixRank n dd) _ _ q) = (sliceClass Finset.univ gen dd).coeff q` at `gen := sliceGen dd hdd`.
  * The rank-two leaf `vSliceValue_sliceGen` (SliceValueV) is closed. But `SliceVFlat`, `SliceVLinesY`, `SliceSplitV` and `SliceValueV` (about 370 lines) index lines by `Fin 3 ⊕ HBlk dd`. They must be generalized to `Fin (n + 1)`, or replaced by a trivial-summand invariance of `LH.chernOf`. A grep found no such invariance.
* `hS₁`, `hSodd`, `tx_inj`: lix-coeff (above).

**Census.** No census rows. This lane's declarations formalize no sentence of the non-MF manuscript.

## NEEDS

* lix-oddside-n: `StepCHalf n (lixDD n j) (KGen.bVecK n (k − 1)) topClass` at the top mod-`p` class.
* Producers of `Gen.ModPStepDData`'s fields over real objects: `TotalH` over `F_p` + Künneth (lix-lh,
  lix-coeff); odd-primary `P^i` with Cartan, `P⁰ = id`, instability (lix-steenrod); Wu with a unit
  leading coefficient, L4a (lix-evenside).

## TRAPS

* `map_mul f a b` / `map_add f a b` with `a b : ↥(evenPart K X)` and `f : TotalHOf K X →+* _` fails with
  "failed to synthesize FunLike (… →+* …) ↥(evenPart K Y) ?m": the argument's subtype fixes the domain
  before the coercion is inserted.  Ascribe `(a : TotalHOf K X)` (probe 0911-232012-91623).

* `NM_UNVERIFIED` refuses a path already on origin/main (even an unverified landing); the in-flight edit
  goes as `NM_ATTIC=1`.
* Name resolution at v4.32 (`Lean/ResolveName.lean`, `resolveUsingNamespace`): the INNERMOST namespace
  with a match wins and open declarations are consulted only when no namespace prefix matches, so a
  `Gen.foo` shadows `CharClass.foo` inside `namespace Gen` without ambiguity.
