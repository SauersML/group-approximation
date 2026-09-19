import GroupApproximation.CharClass.LemmaTwoStepA
import GroupApproximation.Analysis.LIXLemmaTwoProp

/-!
# From the toolkits to Lemma 2, and to the endpoint's named proposition

Lane `cc-lix-odd` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3).

`CharClass/LemmaTwoStepA.lean` reduces Lemma 2 to its two cohomological steps.  This file
closes the two remaining seams:

* **the Step C input**, unconditionally.  For *every* unitary `G` that Step A can produce,
  the manuscript's section of the mapping torus exists, is continuous, is a section, and
  vanishes at exactly one point of `S¹ × M`.  Nothing here is hypothetical; the bump
  function is `sin (π τ)`, whose three needed values are `Real.sin_zero`, `Real.sin_pi`
  and `Real.sin_pi_div_two`, so no bump-function construction and no `χ` hypotheses
  survive.
* **the Step D seam**, `stepD_of_parity`: `cc-wu`'s `gamma_top_eq_zero_of_slice_totalH`
  is exactly `topClass (W_g) = 0` once `topClass` is the top mod-2 Chern class, so the
  glue is one implication.

Finally `lemmaTwoHolds_of` turns the two steps, at every stage of the tower, into
`cs-endpoint`'s `LIX.LemmaTwoHolds` — the single topological input of the endpoint.

## Main results

* `lixChi` — the bump `sin (π τ)`, with `lixChi_zero`, `lixChi_one`, `lixChi_half`.
* `lixZeroPoint`, `lixSection` — the zero and the section, concretely.
* `lixSection_continuous`, `lixSection_mem`, `lixSection_eq_zero_iff` — **the Step C
  input**: exactly one zero, at `(southPole, (-e₃, basePoints))`.
* `stepD_of_parity` — the Step D seam.
* `LemmaTwoInput`, `lemmaTwo_of_input`, `lemmaTwoHolds_of` — Lemma 2 and the endpoint's
  proposition, over the two steps alone.
-/

noncomputable section

namespace GroupApproximation.CharClass

open scoped Matrix
open GroupApproximation.STW59
open GroupApproximation.AlgTop.CPn

set_option linter.unusedSectionVars false

/-! ## 1. The bump function -/

/-- The manuscript's `χ`, taken to be `sin (π τ)`.  The zero-locus argument constrains it
only at `0`, `1/2` and `1`, and the sine is analytic, so strict differentiability of the
section costs nothing and no bump-function construction is needed. -/
def lixChi (τ : ℝ) : ℝ := Real.sin (Real.pi * τ)

@[simp] theorem lixChi_zero : lixChi 0 = 0 := by
  rw [lixChi, mul_zero, Real.sin_zero]

@[simp] theorem lixChi_one : lixChi 1 = 0 := by
  rw [lixChi, mul_one, Real.sin_pi]

@[simp] theorem lixChi_half : lixChi (1 / 2 : ℝ) = 1 := by
  rw [lixChi, show Real.pi * (1 / 2 : ℝ) = Real.pi / 2 by ring, Real.sin_pi_div_two]

theorem continuous_lixChi : Continuous lixChi :=
  Real.continuous_sin.comp (continuous_const.mul continuous_id)

/-! ## 2. The circle point of the zero -/

/-- A point of the circle is determined by its two coordinates. -/
theorem sphereOne_ext {z w : ↥sphereOne} (h0 : circHoriz z = circHoriz w)
    (h1 : circHeight z = circHeight w) : z = w := by
  refine Subtype.ext ?_
  ext i
  fin_cases i
  · exact h0
  · exact h1

theorem eq_southPole {z : ↥sphereOne} (h0 : circHoriz z = 0) (h1 : circHeight z = -1) :
    z = southPole :=
  sphereOne_ext (by rw [h0, circHoriz_southPole]) (by rw [h1, circHeight_southPole])

/-! ## 3. The section, for an arbitrary Step A unitary -/

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ}

/-- The single zero of the section, in the base: `(-e₃, (basePoint)ⱼ)`. -/
def lixZeroPoint (dd : Fin ℓ → ℕ) : baseM dd := (negEThree, baseYPoint dd)

/-- The manuscript's section of the mapping torus `W_g`, at the concrete data. -/
def lixSection (G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ)
    (p : ↥sphereOne × baseM dd) : VIdx dd ⊕ VIdx dd → ℂ :=
  mtSection Vmat G circHoriz circHeight (blockNorth aVec)
    (blockSouth aVec bVec cVec lixChi circHoriz) p

variable {G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ}

/-- The manuscript's pair really is section data for `W_g`, given only Step A's seam. -/
theorem lixSectionData (hGe : ∀ m, G m *ᵥ Sum.elim (aVec m) 0 = Sum.elim (bVec m) 0) :
    IsMTSectionData Vmat G circHoriz circHeight (blockNorth aVec)
      (blockSouth (Z := ↥sphereOne) aVec bVec cVec lixChi circHoriz) :=
  isMTSectionData_manuscriptData isCircleChart_sphereOne continuous_lixChi lixChi_zero
    lixChi_one hGe

theorem lixSection_continuous (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVec m) 0 = Sum.elim (bVec m) 0) :
    Continuous (lixSection G) :=
  mtSection_continuous (lixSectionData hGe) hGu isCircleChart_sphereOne continuous_Vmat hGc

theorem lixSection_mem (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
    (p : ↥sphereOne × baseM dd) :
    mappingTorus Vmat G circHoriz circHeight p *ᵥ lixSection G p = lixSection G p :=
  mtSection_mem hGu isCircleChart_sphereOne p

/-- **The Step C input.**  The section of `W_g` vanishes at exactly one point of
`S¹ × S⁵ × Y`: the south pole of the circle paired with `(-e₃, (basePoint)ⱼ)`. -/
theorem lixSection_eq_zero_iff
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVec m) 0 = Sum.elim (bVec m) 0)
    (p : ↥sphereOne × baseM dd) :
    lixSection G p = 0 ↔ p = (southPole, lixZeroPoint dd) := by
  rw [lixSection, manuscriptSection_eq_zero_iff_concrete isCircleChart_sphereOne
    (lixSectionData hGe) lixChi_half p]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine Prod.ext (eq_southPole h2 h1) (Prod.ext h3 h4)
  · intro h
    subst h
    exact ⟨circHeight_southPole, circHoriz_southPole, rfl, rfl⟩

/-! ## 4. The Step D seam -/

/-- **Step D, glued.**  `cc-wu`'s even side gives `γ_{(∑ⱼ dⱼ)+3}(W_g) = 0`; once
`topClass` *is* that class, the glue is one implication.  `parity` is `cc-wu`'s
`ParityInstance` at the mapping torus and `hlink` is the identification of `topClass` with
`γ`, both definitional once the cohomology layer lands. -/
theorem stepD_of_parity {R H : Type*} [CommRing R] [CommRing H] {K : Type*} [Zero K]
    (topClass : (↥sphereOne × baseM dd →
      Matrix (VIdx dd ⊕ VIdx dd) (VIdx dd ⊕ VIdx dd) ℂ) → K)
    (hd : ∀ j, Even (dd j))
    (parity : ∀ (G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ), Continuous G →
      (∀ m, IsCornerUnitary (Vmat m) (G m)) → LIXParityInput R H dd)
    (hlink : ∀ G hc hu, (parity G hc hu).data.γ ((∑ j, dd j) + 3) = 0 →
      topClass (mappingTorus Vmat G circHoriz circHeight) = 0) :
    ∀ G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ, Continuous G →
      (∀ m, IsCornerUnitary (Vmat m) (G m)) →
      topClass (mappingTorus Vmat G circHoriz circHeight) = 0 :=
  fun G hc hu => hlink G hc hu ((parity G hc hu).gamma_top_eq_zero hd)

/-! ## 5. Lemma 2, and the endpoint's proposition -/

/-- **The two cohomological inputs of Lemma 2 at one index family**, bundled so that they
can be quantified over the tower.  `K` is the coefficient object — in the intended
instance `cc-projective`'s `TotalH` of `N` — and `topClass` the top mod-2 Chern class. -/
def LemmaTwoInput (dd : Fin ℓ → ℕ) : Prop :=
  ∃ (K : Type) (_ : Zero K)
    (topClass : (↥sphereOne × baseM dd →
      Matrix (VIdx dd ⊕ VIdx dd) (VIdx dd ⊕ VIdx dd) ℂ) → K),
    (∀ G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ, Continuous G →
        (∀ m, IsCornerUnitary (Vmat m) (G m)) →
        (∀ m, G m *ᵥ Sum.elim (aVec m) 0 = Sum.elim (bVec m) 0) →
        topClass (mappingTorus Vmat G circHoriz circHeight) ≠ 0) ∧
      ∀ G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ, Continuous G →
        (∀ m, IsCornerUnitary (Vmat m) (G m)) →
        topClass (mappingTorus Vmat G circHoriz circHeight) = 0

/-- **Lemma 2 from the two steps.** -/
theorem lemmaTwo_of_input (h : LemmaTwoInput dd) :
    ¬ ContinuousMvNEquiv (FHmat (dd := dd)) EHmat := by
  obtain ⟨K, hK, topClass, hC, hD⟩ := h
  letI : Zero K := hK
  exact lemmaTwo_of_stepC_stepD topClass hC hD

/-- **Lemma 2 in the C*-side vocabulary, from the two steps.** -/
theorem lemmaTwo_matrix_of_input (h : LemmaTwoInput dd) :
    ¬ MurrayVonNeumannEquiv (toMatC (FHmat (dd := dd)) continuous_FHmat)
      (toMatC (EHmat (dd := dd)) continuous_EHmat) := by
  obtain ⟨K, hK, topClass, hC, hD⟩ := h
  letI : Zero K := hK
  exact lemmaTwo_matrix_of_stepC_stepD topClass hC hD

/-- **The endpoint's single topological input.**  `cs-endpoint`'s `LIX.LemmaTwoHolds`
follows from the two cohomological steps at every stage of the tower, and from nothing
else: Step A is a theorem and the section is unconditional. -/
theorem lemmaTwoHolds_of (h : ∀ j : ℕ, LemmaTwoInput (LIX.lixDD j)) : LIX.LemmaTwoHolds :=
  fun j => lemmaTwo_of_input (h j)

end GroupApproximation.CharClass
