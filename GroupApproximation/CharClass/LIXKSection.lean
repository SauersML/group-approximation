import GroupApproximation.CharClass.LIXKMap
import GroupApproximation.CharClass.LemmaTwoGlue
import GroupApproximation.Meta.AxiomGuard

/-!
# The manuscript's section with `a = e₁` and `b = Ψ_k ∘ x`, and its `k+1` zeros

Lane `sp-oddside` of the STW Problem LIX strengthening
(`notes/LIX_STRONGER_PROGRAM_2026-09-10.md` §1.2, §1.3.4).

`CharClass/LemmaTwoZero.lean`'s `mtSection_manuscript_eq_zero_iff` locates the zero of the
transported section for **abstract** block data `(a, b, c)`: it vanishes at the south pole
of the circle, at the base points where `b = −a` and `c = 0`.  Nothing in it is specific to
`e₃` or to the tautological `x`, and nothing in it mentions the Step A unitary `G`.  So the
`k`-zero geometry is one substitution,

```text
  a := e₁ (constant) ,      b := Ψ_k ∘ x ,      c := the manuscript's transverse section,
```

made in a new concrete instance beside `CharClass/LIXSectionManuscript.lean`, which is left
untouched and stays green.  `LemmaTwoZero.lean` is reused verbatim.

## Why the constant section had to move

With `a = e₃` the zero sits at `x = −e₃`, a suspension point of the clutching coordinate
`Re (x 2)`; a hemisphere-preserving self-map of `S⁵` is a cone there, so no `k`-fold map is
a local homeomorphism at it.  With `a = e₁` the zeros are the `k+1` points `ζ_j e₁` with
`ζ_j^{k+1} = −1`, all on the **equator** (`LIXKMap.re_kZeroVec_two`), and `Ψ_k` is a local
homeomorphism at each because the first coordinate there is nonzero.

## What is unchanged

The transverse block: `cVec`, `cVec_eq_zero_iff`, `Vmat`, `Vmat_mulVec_left`,
`Vmat_mulVec_right`, `lixChi` and the circle chart are the existing ones, imported and not
restated.  The only two fields that change are `a` and `b`, and the only two hypotheses of
`mtSection_manuscript_eq_zero_iff` they touch are `a m ≠ 0`, `∑‖a m i‖² = 1` and
`∑‖b m i‖² = 1`, all three of which are one line each.

## Main results

* `aVecK`, `bVecK` — the two new fields, with their norms and continuity.
* `isMTSectionData_manuscriptDataK` — the pair is section data for `W_g`, given Step A's
  seam `G *ᵥ (e₁, 0) = (Ψ_k x, 0)`.
* `bVecK_eq_neg_aVecK_iff` — the trivial-block condition is `x = ζ_j e₁` for some `j`.
* `lixKSection`, `lixKZero`, `lixKSection_eq_zero_iff` — **the Step C input with `k+1`
  zeros**: the section vanishes exactly at the `k+1` points
  `(southPole, (ζ_j e₁, basePoint))`.
* `lixKZero_injective`, `finite_lixKZeroSet` — the zeros are distinct and finite in number.
-/

noncomputable section

namespace GroupApproximation.CharClass

open scoped Matrix
open GroupApproximation.STW59
open GroupApproximation.AlgTop.CPn

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ}

/-! ## 1. The two new fields -/

/-- The constant section of the trivial block, moved from `e₃` to `e₁`. -/
def aVecK (_m : baseM dd) : Fin 3 → ℂ := eOne

/-- The transported section of the trivial block: the tautological point of `S⁵` composed
with the `k`-fold map.  At `k = 0` this is the tautological point itself. -/
def bVecK (k : ℕ) (m : baseM dd) : Fin 3 → ℂ := psiVec k (m.1 : Fin 3 → ℂ)

theorem aVecK_normSq (m : baseM dd) : ∑ i, ‖aVecK m i‖ ^ 2 = 1 := eOne_normSq

theorem aVecK_ne_zero (m : baseM dd) : aVecK m ≠ 0 := eOne_ne_zero

theorem continuous_aVecK : Continuous (aVecK (dd := dd)) := continuous_const

theorem bVecK_normSq (k : ℕ) (m : baseM dd) : ∑ i, ‖bVecK k m i‖ ^ 2 = 1 := by
  rw [bVecK, normSq_psiVec]
  exact mem_unitVectors_iff.mp m.1.2

theorem continuous_bVecK (k : ℕ) : Continuous (bVecK (dd := dd) k) :=
  (continuous_psiVec k).comp (continuous_subtype_val.comp continuous_fst)

theorem bVecK_zero_eq (m : baseM dd) : bVecK 0 m = bVec m := by
  rw [bVecK, bVec, psiVec_zero_eq]

/-! ## 2. The section data -/

variable {Z : Type*} [TopologicalSpace Z] {y t : Z → ℝ}

/-- **The `k`-fold pair is section data for `W_g`.**  Every hypothesis is discharged here
except the seam `G *ᵥ (e₁, 0) = (Ψ_k x, 0)`, which is Step A's and is where the `k`-th
power of the seam generator enters. -/
theorem isMTSectionData_manuscriptDataK {k : ℕ}
    {G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ} {χ : ℝ → ℝ}
    (hch : IsCircleChart y t) (hχ : Continuous χ) (hχ0 : χ 0 = 0) (hχ1 : χ 1 = 0)
    (hGa : ∀ m : baseM dd, G m *ᵥ Sum.elim (aVecK m) 0 = Sum.elim (bVecK k m) 0) :
    IsMTSectionData Vmat G y t (blockNorth aVecK)
      (blockSouth (Z := Z) aVecK (bVecK k) cVec χ y) :=
  isMTSectionData_blockSplit hch continuous_aVecK (continuous_bVecK k) continuous_cVec hχ
    hχ0 hχ1 (fun m => Vmat_mulVec_left m (aVecK m)) (fun m => Vmat_mulVec_left m (bVecK k m))
    Vmat_mulVec_right hGa

/-! ## 3. The trivial-block condition -/

/-- The `j`-th zero in the base `M = S⁵ × Y`. -/
def lixKZeroPoint (k : ℕ) (dd : Fin ℓ → ℕ) (j : Fin (k + 1)) : baseM dd :=
  (kZero k j, baseYPoint dd)

/-- **The trivial-block condition of the zero locus.**  `Ψ_k x = −e₁` says the sphere
coordinate is one of the `k+1` roots on the `e₁`-axis. -/
theorem bVecK_eq_neg_aVecK_iff (k : ℕ) (m : baseM dd) :
    bVecK k m = -aVecK m ↔ ∃ j : Fin (k + 1), m.1 = kZero k j := by
  rw [bVecK, aVecK, psiVec_eq_neg_eOne_iff]
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨j, Subtype.ext hj⟩
  · rintro ⟨j, hj⟩
    exact ⟨j, congrArg Subtype.val hj⟩

/-! ## 4. The section, and its `k+1` zeros -/

variable {G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ}

/-- The `k`-fold section of the mapping torus `W_g`, at the concrete data. -/
def lixKSection (k : ℕ) (G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ)
    (p : ↥sphereOne × baseM dd) : VIdx dd ⊕ VIdx dd → ℂ :=
  mtSection Vmat G circHoriz circHeight (blockNorth aVecK)
    (blockSouth aVecK (bVecK k) cVec lixChi circHoriz) p

/-- The `k`-fold pair really is section data, given only Step A's seam. -/
theorem lixKSectionData {k : ℕ}
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK m) 0 = Sum.elim (bVecK k m) 0) :
    IsMTSectionData Vmat G circHoriz circHeight (blockNorth aVecK)
      (blockSouth (Z := ↥sphereOne) aVecK (bVecK k) cVec lixChi circHoriz) :=
  isMTSectionData_manuscriptDataK isCircleChart_sphereOne continuous_lixChi lixChi_zero
    lixChi_one hGe

theorem lixKSection_continuous {k : ℕ} (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK m) 0 = Sum.elim (bVecK k m) 0) :
    Continuous (lixKSection k G) :=
  mtSection_continuous (lixKSectionData hGe) hGu isCircleChart_sphereOne continuous_Vmat hGc

theorem lixKSection_mem (k : ℕ) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
    (p : ↥sphereOne × baseM dd) :
    mappingTorus Vmat G circHoriz circHeight p *ᵥ lixKSection k G p = lixKSection k G p :=
  mtSection_mem hGu isCircleChart_sphereOne p

/-- The `j`-th zero, as a point of `N = S¹ × S⁵ × Y`. -/
def lixKZero (k : ℕ) (dd : Fin ℓ → ℕ) (j : Fin (k + 1)) : ↥sphereOne × baseM dd :=
  (southPole, lixKZeroPoint k dd j)

/-- **The Step C input with `k+1` zeros.**  The section of `W_g` vanishes exactly at the
`k+1` points `(southPole, (ζ_j e₁, basePoint))`.  At `k = 0` this is the one-zero statement
of `LemmaTwoGlue.lixSection_eq_zero_iff`, with `e₃` replaced by `e₁`. -/
theorem lixKSection_eq_zero_iff {k : ℕ}
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK m) 0 = Sum.elim (bVecK k m) 0)
    (p : ↥sphereOne × baseM dd) :
    lixKSection k G p = 0 ↔ ∃ j : Fin (k + 1), p = lixKZero k dd j := by
  rw [lixKSection, mtSection_manuscript_eq_zero_iff isCircleChart_sphereOne
    (lixKSectionData hGe) aVecK_ne_zero aVecK_normSq (bVecK_normSq k) lixChi_half p]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    obtain ⟨j, hj⟩ := (bVecK_eq_neg_aVecK_iff k p.2).mp h3
    refine ⟨j, ?_⟩
    rw [lixKZero, lixKZeroPoint]
    exact Prod.ext (eq_southPole h2 h1)
      (Prod.ext hj ((cVec_eq_zero_iff p.2).mp h4))
  · rintro ⟨j, rfl⟩
    refine ⟨circHeight_southPole, circHoriz_southPole, ?_, ?_⟩
    · exact (bVecK_eq_neg_aVecK_iff k _).mpr ⟨j, rfl⟩
    · exact (cVec_eq_zero_iff _).mpr rfl

/-! ## 5. The zeros are `k+1` distinct points -/

theorem lixKZeroPoint_injective (k : ℕ) (dd : Fin ℓ → ℕ) :
    Function.Injective (lixKZeroPoint k dd) := by
  intro a b hab
  exact kZero_injective k (congrArg Prod.fst hab)

theorem lixKZero_injective (k : ℕ) (dd : Fin ℓ → ℕ) :
    Function.Injective (lixKZero k dd) := by
  intro a b hab
  exact lixKZeroPoint_injective k dd (congrArg Prod.snd hab)

/-- The zero set, as a subset of `N`. -/
def lixKZeroSet (k : ℕ) (dd : Fin ℓ → ℕ) : Set (↥sphereOne × baseM dd) :=
  Set.range (lixKZero k dd)

theorem finite_lixKZeroSet (k : ℕ) (dd : Fin ℓ → ℕ) : (lixKZeroSet k dd).Finite :=
  Set.finite_range _

theorem lixKZeroSet_nonempty (k : ℕ) (dd : Fin ℓ → ℕ) : (lixKZeroSet k dd).Nonempty :=
  ⟨lixKZero k dd 0, Set.mem_range_self 0⟩

theorem mem_lixKZeroSet_iff (k : ℕ) (dd : Fin ℓ → ℕ) (p : ↥sphereOne × baseM dd) :
    p ∈ lixKZeroSet k dd ↔ ∃ j : Fin (k + 1), p = lixKZero k dd j := by
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨j, hj.symm⟩
  · rintro ⟨j, hj⟩
    exact ⟨j, hj.symm⟩

/-- **The section is nonzero off the zero set**, which is the form the bundle-pair layer
consumes (`LIXBundlePair.lixSectionTotal_mapsTo` at `k` zeros). -/
theorem lixKSection_ne_zero_of_notMem {k : ℕ}
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK m) 0 = Sum.elim (bVecK k m) 0)
    {p : ↥sphereOne × baseM dd} (hp : p ∉ lixKZeroSet k dd) :
    lixKSection k G p ≠ 0 := by
  intro h
  exact hp ((mem_lixKZeroSet_iff k dd p).mpr ((lixKSection_eq_zero_iff hGe p).mp h))

/-! Audited on every build. -/

#audit_axioms lixKSection_eq_zero_iff
#audit_axioms lixKZero_injective

end GroupApproximation.CharClass
