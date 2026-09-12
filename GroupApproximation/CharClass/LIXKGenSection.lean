import GroupApproximation.CharClass.LIXKGenMap
import GroupApproximation.CharClass.LIXKSection
import GroupApproximation.Meta.AxiomGuard

/-!
# The manuscript's section with `a = e₀` and `b = Ψ_k ∘ x`, at general rank

Lane `sp-oddside-n` of the STW Problem LIX strengthening
(`notes/LIX_STRONGER_PROGRAM_2026-09-10.md` §1.2, §1.3.4; report
`notes/lix-stronger-lane-reports/sp-oddside-n.md` §0.3 file D).

`CharClass/LemmaTwoZero.lean`'s `mtSection_manuscript_eq_zero_iff` locates the zero of the
transported section for **abstract** block data `(a, b, c)` over an abstract pair of index
types.  It is therefore free in the rank as well as in `a` and `b`, and `ι := Fin (n+1)`,
`κ := HIdx dd` is a legal instantiation with nothing to prove.  So the `k`-zero geometry at
rank `n` is the same single substitution `sp-oddside` made at rank two,

```text
  a := e₀ (constant) ,      b := Ψ_k ∘ x ,      c := sp-tower's Gen.cVec,
```

made over `sp-tower`'s `CharClass.Gen` shape layer.  Neither `LemmaTwoZero.lean` nor
`LIXShapeGeneric.lean` nor `LIXKSection.lean` is touched.

## What is unchanged

The transverse block and the circle: `Gen.cVec`, `Gen.cVec_eq_zero_iff`, `Gen.Vmat`,
`Gen.Vmat_mulVec_left`, `Gen.Vmat_mulVec_right`, `lixChi`, `southPole`, `eq_southPole` and
`isCircleChart_sphereOne` are the existing ones, imported and not restated.  The only two
fields that change are `a` and `b`, and the only three hypotheses of
`mtSection_manuscript_eq_zero_iff` they touch are `a m ≠ 0`, `∑‖a m i‖² = 1` and
`∑‖b m i‖² = 1`, one line each.

## Main results

* `KGen.aVecK`, `KGen.bVecK` — the two new fields, with norms and continuity.
* `KGen.isMTSectionData_manuscriptDataK` — the pair is section data for `W_g`, given Step
  A's seam `G *ᵥ (e₀, 0) = (Ψ_k x, 0)`.
* `KGen.lixKSection`, `KGen.lixKZero`, **`KGen.lixKSection_eq_zero_iff`** — the Step C
  input with `k+1` zeros, at every rank.
* `KGen.lixKZero_injective`, `KGen.finite_lixKZeroSet` — the zeros are distinct and finite.
* §6 — the rank-two bridges to `sp-oddside`'s names.
-/

noncomputable section

namespace GroupApproximation.CharClass

namespace KGen

open scoped Matrix
open GroupApproximation.STW59

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ}

/-! ## 1. The two new fields -/

/-- The constant section of the trivial block, at `e₀` rather than at `Gen.eLast n`. -/
def aVecK (n : ℕ) (_m : Gen.baseM n dd) : Fin (n + 1) → ℂ := eZero n

/-- The transported section of the trivial block: the tautological point of `S^{2n+1}`
composed with the `k`-fold map.  At `k = 0` this is the tautological point itself. -/
def bVecK (n k : ℕ) (m : Gen.baseM n dd) : Fin (n + 1) → ℂ :=
  psiVec n k (m.1 : Fin (n + 1) → ℂ)

theorem aVecK_normSq (n : ℕ) (m : Gen.baseM n dd) : ∑ i, ‖aVecK n m i‖ ^ 2 = 1 :=
  eZero_normSq n

theorem aVecK_ne_zero (n : ℕ) (m : Gen.baseM n dd) : aVecK n m ≠ 0 := eZero_ne_zero n

theorem continuous_aVecK (n : ℕ) : Continuous (aVecK (dd := dd) n) := continuous_const

theorem bVecK_normSq (n k : ℕ) (m : Gen.baseM n dd) : ∑ i, ‖bVecK n k m i‖ ^ 2 = 1 := by
  rw [bVecK, normSq_psiVec]
  exact mem_unitVectors_iff.mp m.1.2

theorem continuous_bVecK (n k : ℕ) : Continuous (bVecK (dd := dd) n k) :=
  (continuous_psiVec n k).comp (continuous_subtype_val.comp continuous_fst)

theorem bVecK_zero_eq (n : ℕ) (m : Gen.baseM n dd) : bVecK n 0 m = Gen.bVec n m := by
  rw [bVecK, psiVec_zero_eq, Gen.bVec]

/-! ## 2. The section data -/

variable {Z : Type*} [TopologicalSpace Z] {y t : Z → ℝ}

/-- **The `k`-fold pair is section data for `W_g`, at every rank.**  Every hypothesis is
discharged here except the seam `G *ᵥ (e₀, 0) = (Ψ_k x, 0)`, which is Step A's and is where
the `(k+1)`-st power of the seam generator enters. -/
theorem isMTSectionData_manuscriptDataK (n : ℕ) {k : ℕ}
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ} {χ : ℝ → ℝ}
    (hch : IsCircleChart y t) (hχ : Continuous χ) (hχ0 : χ 0 = 0) (hχ1 : χ 1 = 0)
    (hGa : ∀ m : Gen.baseM n dd,
      G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0) :
    IsMTSectionData (Gen.Vmat n) G y t (blockNorth (aVecK n))
      (blockSouth (Z := Z) (aVecK n) (bVecK n k) (fun m => Gen.cVec m.2) χ y) :=
  isMTSectionData_blockSplit hch (continuous_aVecK n) (continuous_bVecK n k)
    (Gen.continuous_cVec.comp' continuous_snd) hχ hχ0 hχ1
    (fun m => Gen.Vmat_mulVec_left n m (aVecK n m))
    (fun m => Gen.Vmat_mulVec_left n m (bVecK n k m))
    (fun m => Gen.Vmat_mulVec_right n m) hGa

/-! ## 3. The trivial-block condition -/

/-- The `j`-th zero in the base `M = S^{2n+1} × Y`. -/
def lixKZeroPoint (n k : ℕ) (dd : Fin ℓ → ℕ) (j : Fin (k + 1)) : Gen.baseM n dd :=
  (kZero n k j, baseYPoint dd)

/-- **The trivial-block condition of the zero locus.**  `Ψ_k x = −e₀` says the sphere
coordinate is one of the `k+1` roots on the `e₀`-axis. -/
theorem bVecK_eq_neg_aVecK_iff (n k : ℕ) (m : Gen.baseM n dd) :
    bVecK n k m = -aVecK n m ↔ ∃ j : Fin (k + 1), m.1 = kZero n k j := by
  rw [bVecK, aVecK, psiVec_eq_neg_eZero_iff]
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨j, Subtype.ext hj⟩
  · rintro ⟨j, hj⟩
    exact ⟨j, congrArg Subtype.val hj⟩

/-! ## 4. The section, and its `k+1` zeros -/

/-- The `k`-fold section of the mapping torus `W_g` at rank `n`. -/
def lixKSection (n k : ℕ)
    (G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ)
    (p : ↥sphereOne × Gen.baseM n dd) : Gen.VIdx n dd ⊕ Gen.VIdx n dd → ℂ :=
  mtSection (Gen.Vmat n) G circHoriz circHeight (blockNorth (aVecK n))
    (blockSouth (aVecK n) (bVecK n k) (fun m => Gen.cVec m.2) lixChi circHoriz) p

/-- The `k`-fold pair really is section data, given only Step A's seam. -/
theorem lixKSectionData (n : ℕ) {k : ℕ}
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0) :
    IsMTSectionData (Gen.Vmat n) G circHoriz circHeight (blockNorth (aVecK n))
      (blockSouth (Z := ↥sphereOne) (aVecK n) (bVecK n k) (fun m => Gen.cVec m.2)
        lixChi circHoriz) :=
  isMTSectionData_manuscriptDataK n isCircleChart_sphereOne continuous_lixChi lixChi_zero
    lixChi_one hGe

theorem lixKSection_continuous (n : ℕ) {k : ℕ}
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0) :
    Continuous (lixKSection n k G) :=
  mtSection_continuous (lixKSectionData n hGe) hGu isCircleChart_sphereOne
    (Gen.continuous_Vmat n) hGc

theorem lixKSection_mem (n k : ℕ)
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (p : ↥sphereOne × Gen.baseM n dd) :
    mappingTorus (Gen.Vmat n) G circHoriz circHeight p *ᵥ lixKSection n k G p
      = lixKSection n k G p :=
  mtSection_mem hGu isCircleChart_sphereOne p

/-- The `j`-th zero, as a point of `N = S¹ × S^{2n+1} × Y`. -/
def lixKZero (n k : ℕ) (dd : Fin ℓ → ℕ) (j : Fin (k + 1)) :
    ↥sphereOne × Gen.baseM n dd :=
  (southPole, lixKZeroPoint n k dd j)

/-- **The Step C input with `k+1` zeros, at every rank.**  The section of `W_g` vanishes
exactly at the `k+1` points `(southPole, (ζ_j e₀, basePoint))`.  At `k = 0` this is
`sp-tower`'s one-zero statement with the constant section moved from `e_last` to `e₀`. -/
theorem lixKSection_eq_zero_iff (n : ℕ) {k : ℕ}
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0)
    (p : ↥sphereOne × Gen.baseM n dd) :
    lixKSection n k G p = 0 ↔ ∃ j : Fin (k + 1), p = lixKZero n k dd j := by
  rw [lixKSection, mtSection_manuscript_eq_zero_iff isCircleChart_sphereOne
    (lixKSectionData n hGe) (aVecK_ne_zero n) (aVecK_normSq n) (bVecK_normSq n k)
    lixChi_half p]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    obtain ⟨j, hj⟩ := (bVecK_eq_neg_aVecK_iff n k p.2).mp h3
    refine ⟨j, ?_⟩
    rw [lixKZero, lixKZeroPoint]
    exact Prod.ext (eq_southPole h2 h1)
      (Prod.ext hj ((Gen.cVec_eq_zero_iff p.2.2).mp h4))
  · rintro ⟨j, rfl⟩
    refine ⟨circHeight_southPole, circHoriz_southPole, ?_, ?_⟩
    · exact (bVecK_eq_neg_aVecK_iff n k _).mpr ⟨j, rfl⟩
    · exact (Gen.cVec_eq_zero_iff _).mpr rfl

/-! ## 5. The zeros are `k+1` distinct points -/

theorem lixKZeroPoint_injective (n k : ℕ) (dd : Fin ℓ → ℕ) :
    Function.Injective (lixKZeroPoint n k dd) := by
  intro a b hab
  exact kZero_injective n k (congrArg Prod.fst hab)

theorem lixKZero_injective (n k : ℕ) (dd : Fin ℓ → ℕ) :
    Function.Injective (lixKZero n k dd) := by
  intro a b hab
  exact lixKZeroPoint_injective n k dd (congrArg Prod.snd hab)

/-- The zero set, as a subset of `N`. -/
def lixKZeroSet (n k : ℕ) (dd : Fin ℓ → ℕ) : Set (↥sphereOne × Gen.baseM n dd) :=
  Set.range (lixKZero n k dd)

theorem finite_lixKZeroSet (n k : ℕ) (dd : Fin ℓ → ℕ) : (lixKZeroSet n k dd).Finite :=
  Set.finite_range _

theorem lixKZeroSet_nonempty (n k : ℕ) (dd : Fin ℓ → ℕ) :
    (lixKZeroSet n k dd).Nonempty :=
  ⟨lixKZero n k dd 0, Set.mem_range_self 0⟩

theorem mem_lixKZeroSet_iff (n k : ℕ) (dd : Fin ℓ → ℕ)
    (p : ↥sphereOne × Gen.baseM n dd) :
    p ∈ lixKZeroSet n k dd ↔ ∃ j : Fin (k + 1), p = lixKZero n k dd j := by
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨j, hj.symm⟩
  · rintro ⟨j, hj⟩
    exact ⟨j, hj.symm⟩

/-- **The section is nonzero off the zero set**, which is the form the bundle-pair layer
consumes. -/
theorem lixKSection_ne_zero_of_notMem (n : ℕ) {k : ℕ}
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0)
    {p : ↥sphereOne × Gen.baseM n dd} (hp : p ∉ lixKZeroSet n k dd) :
    lixKSection n k G p ≠ 0 := by
  intro h
  exact hp ((mem_lixKZeroSet_iff n k dd p).mpr ((lixKSection_eq_zero_iff n hGe p).mp h))

end KGen

/-! ## 6. The rank-two bridges

Each is `sp-oddside`'s rank-two declaration read at `n = 2`.  They cross `Fin 3` versus
`Fin (2+1)` and `baseM dd` versus `Gen.baseM 2 dd`, both of which `sp-tower` proved
definitional, and no `Decidable` instance is written two ways. -/

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ}

theorem aVecK_two (m : baseM dd) : KGen.aVecK 2 m = aVecK m := rfl

theorem bVecK_two (k : ℕ) (m : baseM dd) : KGen.bVecK 2 k m = bVecK k m := rfl

theorem lixKZeroPoint_two (k : ℕ) (dd : Fin ℓ → ℕ) (j : Fin (k + 1)) :
    KGen.lixKZeroPoint 2 k dd j = lixKZeroPoint k dd j := rfl

theorem lixKZero_two (k : ℕ) (dd : Fin ℓ → ℕ) (j : Fin (k + 1)) :
    KGen.lixKZero 2 k dd j = lixKZero k dd j := rfl

theorem lixKSection_two (k : ℕ) (G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ)
    (p : ↥sphereOne × baseM dd) : KGen.lixKSection 2 k G p = lixKSection k G p := rfl

theorem lixKZeroSet_two (k : ℕ) (dd : Fin ℓ → ℕ) :
    KGen.lixKZeroSet 2 k dd = lixKZeroSet k dd := rfl

/-! Audited on every build. -/

#audit_axioms KGen.lixKSection_eq_zero_iff
#audit_axioms KGen.lixKZero_injective
#audit_axioms KGen.isMTSectionData_manuscriptDataK

end GroupApproximation.CharClass
