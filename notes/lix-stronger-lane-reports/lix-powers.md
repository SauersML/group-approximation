# Lane `lix-powers` (successor of sp-powers): final report, 2026-09-12

Clone: lix-a (shared with lix-tower, lix-oddside-n; rule 20). Owns `Analysis/LIXPowers*` and, by lead assignment,
`CharClass/LIXKGenOf*` (Model, Bundle, Punctured, TopLine, StepC).

## STOPPED 2026-09-12
Lead ruling of 09-12 (`LIX_LANES.md` "STOPPED"): LIX is too low impact, and the LIX-stronger program stops.
- Nothing of this lane is in flight. Every local `LIXPowers*`/`LIXKGenOf*` blob equals a blob landed on main, no probe is
  running, and nothing was deleted.
- The next target was cancelled before any authoring. It was the K-forms of `lixChern`, `lixThomClassTerm`,
  `lixChern_top_eq_gamma` and `lixHclass` for `KZeroStepCDataOf`. Their target statements are under RESIDUAL (d).

## RULINGS
- Sphere hypothesis `IsSphereUnitary` (ContinuousOn off 0, unitary off 0): confirmed by the lead and lix-tower, 09-11 21:35.
- Ruled pair e₁ := −ε(0,0), e₂ := −ε(0,1) on E n; exponent k ↔ `KGen.bVecK n (k − 1)`.
- `clutch u = FHmat`: off the critical path, not built.

## GREEN
Checked on 09-12: the md5 of each origin blob was compared with the probe records and with the probe base commits.
- **Probe 0911-230906-80909, GREEN, base c0c8041cd.**
  - Module: `Analysis/LIXPowersEquatorChart`.
  - Its import closure: `LIXPowersEquator` → `LIXPowersSphere` → `LIXPowersHomotopy` → `LIXPowersNormalise` →
    `LIXPowersPinch` → `LIXPowersAngle` → {`LIXPowersJoinPower`, `LIXPowersEH`} → `LIXPowersNaturality` →
    `LIXPowersGauge`.
  - All eleven files are byte-identical at the base and on origin.
- **Probe 0912-000545-25287, GREEN, base 948130d79.**
  - Modules: `CharClass/LIXKGenOfPunctured`, `LIXKGenOfTopLine`, `LIXKGenOfStepC`.
  - `LIXKGenOfModel` is in the StepC closure and is byte-identical at the base and on origin.
- **Probe 0911-235019-94069, GREEN, base 9c0a4f8ce.** Module: `CharClass/LIXKGenOfBundle`. The file is byte-identical
  at the base and on origin (blob 6627a51a9).
- `Analysis/LIXPowersChain` and `LIXPowersExport`: no lane probe record.
  - Both were last changed in e76e62198.
  - Export imports Chain and has been root-imported since wiring commit 4a49dba9c.
- Root imports on main:
  - `LIXPowersAngle` (d02e576c7).
  - `LIXPowersExport`, `LIXPowersNormalise`, `LIXPowersPinch` (4a49dba9c).
  - `LIXPowersSphere` (edc26bc89).
  - `LIXKGenOfStepC` (bfbe000c7, 09-12 09:36). None of the five `LIXKGenOf*` files has changed since.
- `LIXPowersEquatorChart` is green, but nothing imports it. It is eligible for root wiring at the lead's discretion.
- **Correction to the 09-11 report.** That report called Sphere compiled under probe 0911-224556-7670 and Equator under
  0911-225717-66906. Both records say `PROBE FAILED rc=1`. The two files are green only through probe 0911-230906-80909.

## UNVERIFIED
- No `.lean` file. Every landed file of the lane is in a green probe closure at its origin bytes. Chain and Export are
  covered by the root build.
- `attic/inflight/lix-powers/GroupApproximation/Analysis/LIXPowersEquator.lean.txt` (2ee2ffbdb) is a text copy,
  superseded by 0890faa0d. It is kept.

## ENDPOINTS (green, on main)
- `Analysis/LIXPowersSphere`, `exists_homotopy_pow_comp_normGen_sphere`:
  - hypotheses: e₁, e₂ orthonormal and `IsSphereUnitary U`;
  - conclusion: a homotopy of unitaries on E∖0 from `(normGen e₁ e₂ U) ^ (k + 1)` to
    `normGen e₁ e₂ U ∘ joinPowNeg e₁ e₂ k` on the unit sphere.
- `Analysis/LIXPowersEquator`, `exists_homotopy_pow_comp_genSphere`: the same at `Gen.genSphere n`, with
  e₁ = −`eqBasis n hn 0` and e₂ = −`eqBasis n hn 1`.
- `Analysis/LIXPowersEquatorChart`, `clutchMat_comp_joinPow_psiUnit`: clutching `Ω ∘ joinPow e₁ e₂ k` at x equals
  clutching Ω at `psiUnit n k x`.
- Other declarations of these three files, as listed in the 09-11 report and now green:
  - Sphere: `IsSphereUnitary` (+ mul/star/pow/compRadial), `continuousOn_reparProd`, `unit_reparProd_sphere`,
    `pinchIdentification_angleRepar_sphere` (through `sphereCut`), `isSphereUnitary_normGen`, `normGen_wall_sphere`,
    `exists_homotopy_pow_comp_sphere`.
  - The Sphere file also has the ball unitary B = `ballWall e₁ e₂ U y := U (wallRetract y + (1−‖y‖)•(−e₁))`, with
    `wallShift_ne_zero`, `isBallUnitary_ballWall`, `ballWall_of_norm_eq_one`, `ballWall_zero`, `normGen_eq_ballWall_mul`.
  - Equator: `joinPowNeg_neg_neg`, `wallRetract_neg_neg`, `eqIdx0`/`eqBasis` orthonormal, `equatorEmb_planeSub`,
    `equatorEmb_joinPow` (= `KGen.psiVec n k ∘ equatorEmb` by definition), `isRadialMap_joinPow_equator`,
    `isSphereUnitary_genSphere`, `genSphere_joinPow`, `ballWall_genSphere_zero`.
  - EquatorChart: `equatorProj`, `isSuspensionChart_unitVectors` (t = Re x_last), `equatorEmb_injective`, `psiUnit`
    (Σψ_k on S^{2n+1}), `psiUnit_height`, `psiUnit_equator`.
- `CharClass/LIXKGenOfStepC`. `KZeroStepCDataOf` (line 134) and `stepCHalf_of_kZeroStepCDataOf` (line 152) are in
  namespace `GroupApproximation.CharClass.KGen`. Verbatim:

```lean
def KZeroStepCDataOf (K : Type) [Field K] (n k : ℕ) (dd : Fin ℓ → ℕ)
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0)
    (gamma : Hmod K (lixN n dd) (2 * lixRank n dd)) : Prop :=
  ∃ (u : relCohomology K (lixTotalPair n hGc hGu) (lixPuncturedInTotal n hGc hGu)
      (2 * lixRank n dd))
    (xloc : ∀ i : Fin (k + 1), relCohomology K (lixN n dd)
      ({lixKZero n k dd i}ᶜ : Set (↥sphereOne × Gen.baseM n dd)) (2 * lixRank n dd))
    (c : Hmod K (lixN n dd) (2 * lixRank n dd)),
    LocalSplit (fun i => lixKRhoOf K n k dd i (2 * lixRank n dd))
        ((lixKSRelOf K n k hGc hGu hGe (2 * lixRank n dd)).hom u) xloc ∧
      (∀ i, xloc i ≠ 0) ∧
      LocalClassesAgree (fun i => lixKJlocOf K n k dd i (2 * lixRank n dd)) xloc c ∧
      (lixJEOf K n hGc hGu (2 * lixRank n dd)).hom u
        = (lixPiStarOf K n hGc hGu (2 * lixRank n dd)).hom gamma

theorem stepCHalf_of_kZeroStepCDataOf (K : Type) [Field K] (n k : ℕ)
    (hk : ((k + 1 : ℕ) : K) ≠ 0) (dd : Fin ℓ → ℕ) (hdd : ∀ j, 0 < dd j)
    (topClass : (↥sphereOne × Gen.baseM n dd →
      Matrix (Gen.VIdx n dd ⊕ Gen.VIdx n dd) (Gen.VIdx n dd ⊕ Gen.VIdx n dd) ℂ) →
        Hmod K (lixN n dd) (2 * lixRank n dd))
    (hdata : ∀ (G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ)
      (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
      (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0),
      KZeroStepCDataOf K n k dd hGc hGu hGe
        (topClass (mappingTorus (Gen.Vmat n) G circHoriz circHeight))) :
    Gen.StepCHalf n dd (bVecK n k) topClass
```

  Also in the file:
  - `KGen.lixK_topClass_ne_zeroOf` (line 93): `gamma ≠ 0` from `hsplit`, `hx : xloc i₀ ≠ 0`, `hloc`, `hk` and
    `hclass`, spelled as in `KZeroStepCDataOf`;
  - `topChernClass_ne_zero_kzeroOf` (line 52, namespace `GroupApproximation.CharClass`): the abstract count over `K`,
    at the local model.

## RESIDUAL
Not authored or elaborated; these are target statements. Each has a named F₂ template on main. The K statement is the
template with these substitutions:
- `ZMod 2` → `K`, `Hmod2` → `Hmod K`, `TotalH` → `TotalHOf K`;
- `tautEulerOf` → the class from (a).

The route is `stepCHalf_of_kZeroStepCDataOf` above; `Gen.StepCHalf` is generic in `{K : Type*} [Zero K]`.

**(a) lix-lh: compact-base Leray–Hirsch over a field.** The template is `LH.lerayHirschGraded_compact`
(LerayHirschCompact.lean): `[CompactSpace X] [Nonempty X] (q : Bundle X ι) (s : ℕ) (hs : ∀ x, q.rank x = s)
(hs1 : 1 ≤ s) : LerayHirschGraded (projMapOf q) (tautEulerOf q) s`.

```lean
theorem LH.lerayHirschGraded_compactOf (K : Type) [Field K] [CompactSpace X] [Nonempty X]
    (hgen : Hmod K (CPtop (1 + tautCardOf ι)) 2)
    (hgenBasis : /- hgen spans Hmod K (CPtop (1 + tautCardOf ι)) 2 -/)
    (q : Bundle X ι) (s : ℕ) (hs : ∀ x, q.rank x = s) (hs1 : 1 ≤ s) :
    LerayHirschGraded (projMapOf q) (LH.tautEulerDualK K hgen q) s
```

- Main has no K Leray–Hirsch theorem on `tautEulerOfK`/`tautEulerDualK`, so no generator hypothesis exists to copy.
- The choice of ξ fixes the sign of every Chern class below. The two candidates are `tautEulerDualK` (= −`tautEulerOfK`)
  and `tautEulerOfK`. lix-thom's sign trap says the splitting (`+`) form needs `tautEulerDualK`.

**(b) lix-thom: the class restrictions over K.**
- The first statement is the `htaut` input of the green `ThomChernDeg.thomData_total_of_tautOf`.
- The second is the K twin of `LH.pull_bridgeChartIncl_tautEulerOf` (ThomChartTautZero.lean:170).

```lean
theorem pull_sInclusion_tautEulerDualK (K : Type) [Field K] [CompactSpace X] [T2Space X]
    (hgen : Hmod K (CPtop (1 + tautCardOf ι)) 2)
    (hgenPlus : Hmod K (CPtop (1 + tautCardOf _)) 2) -- at the index type of `p.plusOne`
    (hcompat : /- hgenPlus restricts to hgen along the block inclusion
      (CPn.bijective_pull_cpBlockInclIterOf) -/)
    (p : Bundle X ι) :
    pull (sInclusion (Set.range (Bundle.projIncl p))) 2 (LH.tautEulerDualK K hgenPlus p.plusOne)
      = pull (hyperIso p).hom 2 (LH.tautEulerDualK K hgen p)

theorem pull_bridgeChartIncl_tautEulerDualK (K : Type) [Field K]
    (hgenPlus : Hmod K (CPtop (1 + tautCardOf _)) 2) (p : Bundle X ι) :
    pull (cmap (bridgeChartIncl p)) 2 (LH.tautEulerDualK K hgenPlus p.plusOne) = 0
```

- For the second, the proof step is lix-thom's
  `rw [CPn.eulerOfBundle_pushforward_congrOf K hN hgen q (triv X (Fin 1)) hf hg hfq hgq e]`.
- `CPn.eulerOfBundle_pushforward_congrOf` is on main (77c5176d3) but unwired.
- The names `pull_sInclusion_tautEulerOf` and `pull_bridgeChartIncl_tautEulerOf` already on main are the F₂ lemmas.

**(c) Generic K ports, over any field.**
- `gamma_of_isoOf`. Template: `LerayHirschGammaIso.gamma_of_iso`. Statement:
  `L.gamma k = (lerayHirschGraded_of_iso e π πQ hπ ξ ξQ hξ L).gamma k`, with `ξ : Hmod K P 2` and `ξQ : Hmod K Q 2`.
- `component_chern_eq_neg_gammaOf`. Template: `ChernGammaComponent.component_chern_eq_gamma`, carrying the K sign of
  `LerayHirschDataEvenOf.chern_relation_lhFunEvenOf`:

  ```lean
  theorem component_chern_eq_neg_gammaOf [Nonempty X] (L : LerayHirschGraded π ξ r) (k : ℕ)
      (hk : 1 ≤ k) (hkr : k ≤ r) :
      TotalHOf.component K X (2 * k) ((LerayHirschDataEvenOf.of_graded L).chern k : TotalHOf K X)
        = -L.gamma k
  ```

- `chernMul_top_unitOf`. Template: `LIXHclass.chernMul_top_unit`. Statement:
  `chernMulOf L ⟨0, hr⟩ (cohCast (show (0 : ℕ) = 2 * r - 2 * r by omega) (one (K := K) X)) = L.gamma r`.
- `pull_bridgeChartIncl_lhSumOf`. Template: `LIXHclass.pull_bridgeChartIncl_lhSum`, over
  `LH.tautEulerDualK K hgenPlus p.plusOne`. It needs the second lemma of (b).
- `pull_eq_absPullOf`. Template: `ThomBridgeRelToAbs.pull_eq_absPull`. Statement:
  `pull f n a = (absPullOf K f n).hom a := rfl`.
- `injective_thomJmTotalOf` and `range_thomJmTotalOf`. Templates: `LIXThomClassTerm.injective_thomJmTotal` and
  `range_thomJmTotal`. They use `thomJmTotalOf` (ThomJmNaturalOf, on main) and
  `L : LerayHirschGraded (projMapOf p.plusOne) (LH.tautEulerDualK K hgenPlus p.plusOne) (r + 1)`.

**(d) lix-powers (cancelled): the rank-n K terms.** Templates: `KGen.lixChern` and `KGen.lixChern_mappingTorus`
(LIXKGenChern), `KGen.lixThomClassTerm` (LIXKGenThomTerm), `KGen.lixHclass` (LIXKGenHclass), and
`KGen.KZeroLocalData` and `kZeroStepCData_of_kZeroLocalData` (LIXKGenStepCHalfTop).

```lean
def KGen.lixChernK (K : Type) [Field K] (n : ℕ) (dd : Fin ℓ → ℕ)
    (hgen : Hmod K (CPtop (1 + tautCardOf (Gen.VIdx n dd ⊕ Gen.VIdx n dd))) 2) :
    ∀ P : LixFamily n dd, Continuous P → (∀ p, IsStarProjection (P p)) →
      ∀ k : ℕ, Hmod K (lixN n dd) (2 * k)
  -- branch as in KGen.lixChern: TotalHOf.component K (lixN n dd) (2 * k)
  --   ((LerayHirschDataEvenOf.of_graded (LH.lerayHirschGraded_compactOf K hgen hgenBasis
  --     (⟨P, hcont, hproj⟩ : Bundle _ _) h.choose h.choose_spec.2 h.choose_spec.1)).chern k)

theorem KGen.lixChernK_mappingTorus -- as KGen.lixChern_mappingTorus, at s := lixRank n dd,
    -- hs := fun x => rank_lixBundle n G hGc hGu x, hs1 := one_le_lixRank n dd

def KGen.lixThomClassTermOf (K : Type) [Field K] (hgenPlus : _) (n : ℕ)
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    ↥(relCohomology K (lixTotalPair n hGc hGu) (lixPuncturedInTotal n hGc hGu)
      (2 * lixRank n dd))

theorem KGen.lixThomClassTermOf_ne_zero … : lixThomClassTermOf K hgenPlus n hGc hGu ≠ 0

theorem KGen.lixHclassOf … :
    (lixJEOf K n hGc hGu (2 * lixRank n dd)).hom (lixThomClassTermOf K hgenPlus n hGc hGu)
      = (lixPiStarOf K n hGc hGu (2 * lixRank n dd)).hom
          (lixChernK K n dd hgen (mappingTorus (Gen.Vmat n) G circHoriz circHeight)
            (continuous_mappingTorus_lix n hGc) (isStarProjection_mappingTorus_lix n hGu)
            (lixRank n dd))

def KGen.KZeroLocalDataOf (K : Type) [Field K] (hgenPlus : _) (n k : ℕ) (dd : Fin ℓ → ℕ)
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0) : Prop :=
  ∃ (xloc : ∀ i : Fin (k + 1), relCohomology K (lixN n dd)
      ({lixKZero n k dd i}ᶜ : Set (↥sphereOne × Gen.baseM n dd)) (2 * lixRank n dd))
    (c : Hmod K (lixN n dd) (2 * lixRank n dd)),
    LocalSplit (fun i => lixKRhoOf K n k dd i (2 * lixRank n dd))
        ((lixKSRelOf K n k hGc hGu hGe (2 * lixRank n dd)).hom
          (lixThomClassTermOf K hgenPlus n hGc hGu)) xloc ∧
      (∀ i, xloc i ≠ 0) ∧
      LocalClassesAgree (fun i => lixKJlocOf K n k dd i (2 * lixRank n dd)) xloc c

theorem KGen.kZeroStepCDataOf_of_kZeroLocalDataOf …
    (h : KZeroLocalDataOf K hgenPlus n k dd hGc hGu hGe) :
    KZeroStepCDataOf K n k dd hGc hGu hGe
      (lixChernK K n dd hgen (mappingTorus (Gen.Vmat n) G circHoriz circHeight)
        (continuous_mappingTorus_lix n hGc) (isStarProjection_mappingTorus_lix n hGu)
        (lixRank n dd))
  -- proof: ⟨lixThomClassTermOf K hgenPlus n hGc hGu, xloc, c, hsplit, hne, hagree, lixHclassOf …⟩
```

- **Sign (not elaborated).** `thomLift_castSucc` (ThomFreeDegreewise.lean:124) is `thomLift g x i.castSucc = −g i x`, so `jE u = π^*(−gamma_r)`. By (c) `component_chern_eq_neg_gammaOf` this is
  `π^*(chern_r)`, which is why `lixHclassOf` carries the ring Chern class.
- **Top class.** `topClass W := if h : Continuous W ∧ ∀ p, IsStarProjection (W p)
  then lixChernK K n dd hgen W h.1 h.2 (lixRank n dd) else 0`. Then `stepCHalf_of_kZeroStepCDataOf` turns
  `∀ G hGc hGu hGe, KZeroLocalDataOf …` into `Gen.StepCHalf n dd (bVecK n k) topClass`, after `dif_pos` on the
  mapping torus.

**(e) Fields owned by other lanes.**
- lix-oddside / lix-oddside-n: `LocalSplit`, `∀ i, xloc i ≠ 0` and `LocalClassesAgree` of `KZeroLocalDataOf`, at
  `u = lixThomClassTermOf`.
- lix-evenside-n: a producer of `Gen.RealBundleModP p (lixDD n j) (T j) (γfun j (mappingTorus (Vmat n) G circHoriz
  circHeight))` for `Gen.lemmaTwoFor_powers_of_stepC_realModP` (CharClass/LIXStepDGenReal.lean:335). No producer exists
  on main.
- The adapter into that consumer. I did not check whether one already exists.
  - The consumer's `hC` asks for `StepCHalf n (lixDD n j) (KGen.bVecK n (k - 1))
    (fun W => γfun j W ((∑ i, lixDD n j i) + (n + 1)))`. It takes values in `TotalHOf K (N j)`, at index
    `lixRank n (lixDD n j)`.
  - (d) gives a topClass with values in `Hmod K (lixN n dd) (2 * lixRank n dd)`.
  - Unchecked route: build `γfun j W m` from `TotalHOf.of K (N j) (2 * m)` of the degree-2m class, and carry
    nonvanishing through `of`. Here `TotalHOf.of K X n : TotalPieceOf K X n →+ TotalHOf K X` (ChernTotalRingOf.lean:110)
    and `TotalPieceOf K X n := Hmod K X n`.
  - The consumer binds `{K : Type} [CommRing K]` with `[∀ j, ExpChar (evenPart K (Y j)) p]`. The green theorem needs
    `[Field K]` and `hk : ((k - 1 + 1 : ℕ) : K) ≠ 0`. I did not check how to reconcile the two.

## SHAS (commits on main touching lane paths, oldest first)
- Landings that include lane files (sp-powers era and batch preserves): 6d8c6a7a1, 8cdb6b3fb, e76e62198, 9d5cf111f,
  00b07a9b9.
- `Analysis/LIXPowers*`: 2f42d479b, dffff86df, 2ee2ffbdb (attic), 0890faa0d, 3e0035c8b, c0c8041cd, 63487f51c.
- `CharClass/LIXKGenOf*`: 664a4c758, 893a25c71, 50ffefe3e, b83b8ce5c, 8b0c32e8f.

## TRAPS
- `tac <;> rfl`, where `tac` leaves exactly one goal, is a HARD error under warningAsError ("Used `tac1 <;> tac2` where
  `(tac1; tac2)` would suffice"). Put `rfl` on its own line. It cost two probe rounds, one per file.
- In a section with `variable (hn : 0 < n)`, a theorem whose STATEMENT does not mention `hn` does not get it, even when
  its proof uses it; write `include hn in`.
- `rw [if_neg h]` rewrites only the `ite`s sharing the first match's branches; use `simp only [if_neg h]` for several.
- `rw [pow_succ]` with two `_ ^ (k+1)` in the goal instantiates on whichever it meets first; pin the base.
- A FAILED probe record still lists md5s. Read its `# PROBE GREEN` / `# PROBE FAILED` line; an md5 match does not make a
  file green.
- The shared working tree is dirty, so a working-tree DIFF against origin does not show unlanded work. Compare the local
  blob with every blob in `git log origin/main -- <path>`.
- A trailing `Of` in a name does not mean K: `pull_sInclusion_tautEulerOf` is an F₂ lemma about `tautEulerOf`. Read the
  statement.
- Over K, `LerayHirschGraded.gamma k = −chern k` for 1 ≤ k ≤ r. The module docstring of `ChernGammaBridgeOf` says so,
  as a consequence of `LerayHirschDataEvenOf.chern_relation_lhFunEvenOf`. No named theorem states it. An F₂ proof that
  reads `gamma` as the Chern class does not port.
- Over K, the Chern classes depend on the chosen generator `hgen`, and "nonzero = generator" fails; use
  `hsu_isUnit_of_ne_zeroOf`.
- F₂ `LIXThomClassTerm`: spell arguments exactly as the discharging theorem does, and use `Eq.trans` rather than `calc`
  across `lixTotalPair` spellings.
- `open Classical in` goes before the docstring.
- zsh cannot parse grep/awk patterns containing `(·|…)` unless they are single-quoted. ERE `\s` and `\b` match nothing
  in `git grep -E`.
