# Lane `lix-oddside`: the local computation at the zeros (leaves (3) `hx`, (4) `hsplit`) at p = 2

This is the relaunched worker of lead `nonsofic-existence-3a`, started after the lead session ended on 2026-09-12 at 00:51 CDT.

- **Rank two (owned):** `CharClass/LIXKLocalSplit`, `LIXKLocalRestrict`, `LIXKStepCExponent`.
- **Rank `n` (owned):** `CharClass/LIXKGenLocalSplit`, `LIXKGenLocalSplitOf`, `LIXKGenLocalEta`, `LIXKGenLocalLinear`. These are written over lix-oddside-n's names.
- **Peer report:** `notes/lix-stronger-lane-reports/lix-oddside-n.md`.

## STOPPED (2026-09-12 ~09:35)

The lane stopped under the user ruling of 09-12, relayed by the lead: "LIX is too low impact. we should only do things HIGHER impact than non-MF". There is no new authoring and there are no new probes.

- **No probe running.** No lix-oddside probe was running at the stop. The last one, 0912-092403-35990, is PROBE GREEN.
- **Nothing in flight.** No lix-oddside file was unlanded or in the attic, so nothing went through NM_UNVERIFIED or NM_ATTIC at wind-down. Nothing was deleted.
- **Hand-offs void.**
  - The lead's wind-down message voided its 09-12 Legs/Square hand-off.
  - lix-cupone withdrew its claim on the chain.
  - lix-oddside-n wrote no Legs or Square code.

## GREEN on main

For every module below:

- a green record has its own COMPILED line for that module, and
- the md5 on origin/main, checked at a30e7e4ca, equals the md5 in that record.

| module | green record | last commit on main | main declarations |
|---|---|---|---|
| `LIXKLocalSplit` | 0911-232049-95044; compiled again in 0912-092403-35990 | b6d871308 | `relCocycleClass`, `relCohomology_eq_zero_of_forall_mem`, `exists_relClass_split_of_acyclic`, **`exists_localSplit_of_acyclic`**, `exists_localSplit_two` |
| `LIXKLocalRestrict` | 0911-232049-95044 (BUILT); compiled again in 0912-092403-35990 | 5816b46dc | **`LIXKRelMV.restrictTo`**, `restrictTo_relPullback_id_eq_zero`, **`LIXKRelMV.xloc_ne_zero_of_restrictTo_ne_zero`**, `kJ`, `kI`, `kRho`, `kJ_hexact`, `kRho_hcompat`, **`LIXKRelMV.topChernClass_ne_zero_kzero_two_of_restrict`** |
| `LIXKStepCExponent` | 0911-232049-95044 (BUILT) | c7f8926dc | `kSwapHomeo`, `lixKSwap`, `lixKExc`, `lixKZeroSet_compl_iff`, **`KLocalNonzero`**, **`lixK_topChern_ne_zero_of_localNonzero`**, **`lixK_topChern_ne_zero_exponent`** |
| `LIXKGenLocalSplit` | 0912-092403-35990 | 20295daef | `lixKZeroSet_compl_iff`, `exists_localSplit_kgen`, **`KGenLocalNonzero`**, `exists_localSplit_ne_zero_kgen`, **`kZeroStepCData_of_localNonzero`** |
| `LIXKGenLocalSplitOf` | 0912-092403-35990 | d6ab186d0 | `LIXKRelMV.exists_localSplitOf`, `exists_localSplit_kgenOf`, **`KGenLocalNonzeroOf`**, `exists_localSplit_ne_zero_kgenOf` |
| `LIXKGenLocalEta` | 0912-092403-35990 | 6d6d4a4e2 | `lixKTau`, `lixKTau_mem`, **`lixKEtaLin`**, `lixKEtaLin_eq_blockSouth`, **`lixKSection_eq_mulVec`**, `Vmat_mulVec_lixKEtaLin`, **`lixKEtaLin_eq_zero_iff`** |
| `LIXKGenLocalLinear` | 0912-092403-35990 (BUILT) | 40ecb054b | **`lixKGFrame`**, `injective_mappingTorus_lixKZero_mulVec`, `lixKGEtaZeroMap`, **`lixKGLin`**, `bijective_lixKGLin`, `lixKGFrame_mulVec_lixKGLin`, `lixKGHomeo`, `lixKGMap`, `lixKGHomeo_mapsTo`, **`relPullback_lixKGHomeo_eq_id`** |

**Probe bases.**

- 0911-232049-95044 is based on 46270ef0c.
- 0912-092403-35990 is based on 2889b6229. Its record covers `LIXKLocalSplit`, `LIXKLocalRestrict`, `LIXKGenLocalSplit`, `LIXKGenLocalSplitOf`, `LIXKGenLocalEta` and `LIXKGenLocalLinear`.

**Landing history.**

- **Unverified landings:** fdc38fd6f, 9aac20358, c7f8926dc, 20295daef, d6ab186d0, 6d6d4a4e2, e92b7f2c9, 40ecb054b.
- **Normal landings:** b6d871308, 46270ef0c, 5816b46dc.
- **Unverified labels on green bytes.** The last commits of `LIXKStepCExponent`, `LIXKGenLocalSplit`, `LIXKGenLocalSplitOf`, `LIXKGenLocalEta` and `LIXKGenLocalLinear` carry the Unverified label. Their bytes did not change after the green probe, so a normal re-land is NOTHING TO LAND.
- **One red probe.** 0912-004633-26292 failed on the unused binder `hGu` in `LIXKGenLocalLinear`. It was renamed `_hGu` at 40ecb054b and passed in 0912-092403-35990.

**Wiring.**

- `GroupApproximation.lean` imports none of the seven, and none is in the wire queue.
- Importers on main:
  - `LIXKLocalSplit` ← `LIXKLocalRestrict`
  - `LIXKLocalRestrict` ← `LIXKGenLocalSplit`, `LIXKStepCExponent`
  - `LIXKGenLocalSplit` ← `LIXKGenLocalSplitOf`
  - `LIXKGenLocalEta` ← `LIXKGenLocalLinear`

UNVERIFIED from this lane: none.

## Never authored

`LIXKGenLocalHomotopy`, `LIXKGenLocalLegs`, `LIXKGenLocalSquare` and `LIXKGenLocalNonzero` do not exist on main. The declarations under "Restart notes" are a plan, not claims.

## Residual: exact statements

### 1. p = 2, rank `n`: `KGenLocalNonzero` at the Thom class

This is the hypothesis `hlocal` of `KGen.kZeroStepCData_of_localNonzero`, from `CharClass/LIXKGenLocalSplit.lean`:
```lean
def KGenLocalNonzero (n k : ℕ) {dd : Fin ℓ → ℕ}
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0)
    (u : relCohomology (ZMod 2) (lixTotalPair n hGc hGu) (lixPuncturedInTotal n hGc hGu)
      (2 * lixRank n dd)) : Prop :=
  ∀ i : Fin (k + 1), ∃ B : Set (↥sphereOne × Gen.baseM n dd),
    (∀ j, j ≠ i → lixKZero n k dd j ∉ B) ∧
      (LIXKRelMV.restrictTo (ZMod 2) (X := lixN n dd) B
          ((lixKZeroSet n k dd)ᶜ : Set (↥sphereOne × Gen.baseM n dd)) (2 * lixRank n dd)).hom
        ((lixKSRel n k hGc hGu hGe (2 * lixRank n dd)).hom u) ≠ 0
```

- **Target:** `KGenLocalNonzero n k hGc hGu hGe (lixThomClassTerm n hGc hGu)`, for all `n k dd G hGc hGu hGe`.
- **Consequence:** through `exists_localSplit_ne_zero_kgen` with `u := lixThomClassTerm n hGc hGu`, it gives statement 2.

### 2. p = 2, rank `n`: `KZeroLocalData`

From `CharClass/LIXKGenStepCHalfTop.lean`, owned by lix-oddside-n:
```lean
def KZeroLocalData (n k : ℕ) (dd : Fin ℓ → ℕ)
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0) : Prop :=
  ∃ xloc : ∀ i : Fin (k + 1), relCohomology (ZMod 2) (lixN n dd)
      ({lixKZero n k dd i}ᶜ : Set (↥sphereOne × Gen.baseM n dd)) (2 * lixRank n dd),
    LocalSplit (fun i => lixKRho n k dd i (2 * lixRank n dd))
        ((lixKSRel n k hGc hGu hGe (2 * lixRank n dd)).hom (lixThomClassTerm n hGc hGu)) xloc ∧
      ∀ i, xloc i ≠ 0
```

**Consumers:**

- `kZeroStepCData_of_kZeroLocalData`
- `stepCHalf_two_lixChernOf`
- `stepCHalf_two_powers_lixChernOf`
- the hypothesis `hloc` of `Gen.lemmaTwoFor_powers_two_lixChernOf` in `CharClass/LIXLemmaTwoGenTwo.lean`. There it reads `KGen.KZeroLocalData n (e - 1) (LIX.Gen.lixDD n j) hGc hGu hGe`, quantified over the exponent, the stage and `G`.

### 3. Rank two: `KLocalNonzero`

From `CharClass/LIXKStepCExponent.lean`:
```lean
def KLocalNonzero (k : ℕ) (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK m) 0 = Sum.elim (bVecK k m) 0) : Prop :=
  ∀ i : Fin (k + 1), ∃ B : Set (↥sphereOne × baseM dd),
    (∀ j, j ≠ i → lixKZero k dd j ∉ B) ∧
      (LIXKRelMV.restrictTo (ZMod 2) (X := lixN dd) B
          ((lixKZeroSet k dd)ᶜ : Set (↥sphereOne × baseM dd)) (2 * lixRank dd)).hom
        ((lixKSRel k hGc hGu hGe (2 * lixRank dd)).hom (lixThomClassTerm hGc hGu)) ≠ 0
```

- **Consumers:** `lixK_topChern_ne_zero_of_localNonzero` and `lixK_topChern_ne_zero_exponent`.
- **Producers:** none on main.

### 4. Over a field `K`: `LocalClassesAgree` inside `KZeroStepCDataOf`

`LocalClassesAgree`, from `CharClass/LIXKCount.lean`:
```lean
def LocalClassesAgree {A : ModuleCat.{0} K} {k : ℕ} {relLoc : Fin k → ModuleCat.{0} K}
    (jloc : ∀ i, relLoc i ⟶ A) (xloc : ∀ i, relLoc i) (c : A) : Prop :=
  ∀ i, (jloc i).hom (xloc i) = c
```

It is one field of `KZeroStepCDataOf`, from `CharClass/LIXKGenOfStepC.lean`. `stepCHalf_of_kZeroStepCDataOf` consumes that definition:
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
```

**What is closed over `K`.** The first two fields follow from the statement below, through `exists_localSplit_ne_zero_kgenOf` (GREEN, `CharClass/LIXKGenLocalSplitOf.lean`):
```lean
def KGenLocalNonzeroOf (K : Type) [Field K] (n k : ℕ) {dd : Fin ℓ → ℕ}
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0)
    (u : relCohomology K (lixTotalPair n hGc hGu) (lixPuncturedInTotal n hGc hGu)
      (2 * lixRank n dd)) : Prop :=
  ∀ i : Fin (k + 1), ∃ B : Set (↥sphereOne × Gen.baseM n dd),
    (∀ j, j ≠ i → lixKZero n k dd j ∉ B) ∧
      (LIXKRelMV.restrictTo K (X := lixN n dd) B
          ((lixKZeroSet n k dd)ᶜ : Set (↥sphereOne × Gen.baseM n dd)) (2 * lixRank n dd)).hom
        ((lixKSRelOf K n k hGc hGu hGe (2 * lixRank n dd)).hom u) ≠ 0
```

**What is open over `K`.**

- `KGenLocalNonzeroOf K n k hGc hGu hGe u` at the `u` of the `jE` field.
- `LocalClassesAgree (fun i => lixKJlocOf K n k dd i (2 * lixRank n dd)) xloc c` for the `xloc` that it produces.

**Over `ZMod 2`.** The agreement field is not needed there: lix-oddside-n's `KZeroStepCData` (`CharClass/LIXKGenStepCHalf.lean`) has no agreement field.

**Odd `p`.** This work was not started.

## Restart notes (plan only; nothing here is proved)

**The rank-`n` local square.** It ports `LIXHsqHomotopy`, `LIXHsqLegs` and `LIXHsq` to `lixKU`, with `B := lixKTrivBall n k dd i hGc hGu`. Names below are as used in the plan; check the spellings on main before using them.

- **Left leg:** `lixKChartPt ≫ sInclusion B ≫ cmap (lixKSectionTotal n k hGc hGu hGe)`.
- **Right leg:** `lixKShrinkMap ≫ lixKIncF ≫ sliceMap (lixKZeroInBall …) ≫ lixKTrivInv ≫ cmap (Bundle.totalInclOn …)`. It computes to `lixKFibreMap`.
- **Homotopy:** `H(s, v) = (lixKBaseChart (s • q), mappingTorus … *ᵥ Sum.elim 0 (lixKEtaLin n (s • q) (lixKProductChart n dd q)))`, with `q = (lixKFC n k dd i).symm v`.
- **Cut:** use `relPullback_eq_of_homotopy_of_line contractibleSpace_lixKI … (lixKULine …)`. Then `relPullback_lixKGHomeo_eq_id` removes the linear end.
- **Nonzero:** combine three facts:
  - `lixKLocalPairIsoClosed_lixKRes_ne_zero` (GREEN, lix-oddside-n)
  - injectivity of the excision pullback along `lixKIncF`
  - `injective_lixKShrink` (GREEN)

**Planned declarations.**

- **`LIXKGenLocalHomotopy`:**
  - `lixKI : Set ℝ := Set.Icc 0 1` and `contractibleSpace_lixKI`.
  - `lixKQ n k dd i hGc hGu v := (lixKFC n k dd i).symm v`.
  - `lixKHomotopyFun … : C(↥lixKI × ↥lixKU, Bundle.Total (lixBundle n G hGc hGu))`.
  - `lixKHomotopy_mapsTo`: maps `{p | p.2 ∈ Subtype.val ⁻¹' {0}ᶜ}` into `lixPuncturedInTotal`.
  - `lixKFibreMap … : C(Fin r → ℂ, Total)`, sending `y` to `⟨(lixKZero n k dd i, lixKGFrame n k i hGc hGu *ᵥ y), _⟩`.
  - `lixKHomotopy_at_one`: equals `lixKSectionTotal n k hGc hGu hGe (lixKBaseChart n k dd i (lixKQ … v))`.
  - `lixKHomotopy_at_zero`: equals `lixKFibreMap … (lixKGLin n k i hGc hGu v)`.
  - `continuous_lixKTau` and `continuous_lixKEtaLin_pair`.
- **`LIXKGenLocalLegs`:**
  - Maps: `lixKIncF`, `lixKTrivInv`, `lixKInclOn`, `lixKSecMap`, `lixKChartPt`.
  - Legs, each with its `mapsTo`: `lixKGLmap`, `lixKGRmap`, `lixKGRmap'`, `lixKFarMap`.
  - `rfl` identifications: `lixKSRel_eq`, `lixKRes_eq`, `lixKBundlePairIso_hom_eq`, `lixKProdIso_hom_eq`, `lixKLocalPairIsoClosed_hom_eq`, `restrictTo_eq`.
  - Evaluation lemmas: `lixKTrivInv_apply`, `lixKGRmap_eq`, `lixKGLmap_apply`, `lixKFarMap_apply`, `lixKHomotopy_end_one`, `lixKHomotopy_end_zero`.
- **`LIXKGenLocalSquare`:** `relPullback_lixKFar_eq_lixKGR'`, `relPullback_lixKGL_eq_lixKGR`, and the shrunk square on `lixKU`. `relPullback_congr_map` is in `LIXHsq.lean`.
- **`LIXKGenLocalNonzero`:** `KGenLocalNonzero n k hGc hGu hGe (lixThomClassTerm n hGc hGu)`, then `KZeroLocalData n k dd hGc hGu hGe`, then a named `Prop` endpoint with `#audit_closed_axioms`.

**Trap.** The unused-binder lint is a hard error under warningAsError. A binder used only in the type needs a `_` prefix.
