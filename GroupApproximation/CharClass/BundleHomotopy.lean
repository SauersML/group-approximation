import GroupApproximation.CharClass.BundleSpace
import Mathlib.Topology.Homotopy.Equiv

/-!
# Complex vector bundles in the projection model, IV: the two contractions

Two deformation retractions, both of them scalings of the fibre:

* `E(p) ≃ X`: contract every fibre to its origin, `(x, v) ↦ (x, t·v)`.
* `E(p) ∖ 0 ≃ S(p)`: push every nonzero vector onto the unit sphere of its
  fibre, `(x, v) ↦ (x, (t + (1-t)‖v‖⁻¹)·v)`.

Both scalings stay inside the fibre because the fibre is the *fixed-point set*
of a linear map, and both are continuous because the fibrewise Euclidean length
is a finite sum of squared moduli.  The second one is the input to the Gysin
sequence of `cc-projective`: the Mayer-Vietoris of
`P(L ⊕ 1) = E(L) ∪ (P(L⊕1) ∖ Z)` has intersection `E(L) ∖ 0`, and it is this
homotopy equivalence that turns that into `S(L)`.

## Manuscript status

Machinery.  Certifies no manuscript step on its own.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open scoped Matrix
open GroupApproximation.STW59
open unitInterval

namespace Bundle

section Scaling

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι]

/-- Rescaling a vector of a fibre keeps it in the fibre: the fibre is the
fixed-point set of a linear map. -/
theorem smul_mem_totalSet {p : Bundle X ι} {v : X × (ι → ℂ)} (hv : v ∈ totalSet p) (c : ℂ) :
    ((v.1, c • v.2) : X × (ι → ℂ)) ∈ totalSet p := by
  show p v.1 *ᵥ (c • v.2) = c • v.2
  rw [Matrix.mulVec_smul, mem_totalSet_iff.mp hv]

/-! ### `E(p)` contracts onto the zero section -/

/-- The scaling homotopy from the zero section to the identity of `E(p)`. -/
def scaleHomotopy (p : Bundle X ι) :
    ContinuousMap.Homotopy ((zeroSection p).comp (totalPi p)) (ContinuousMap.id (Total p)) where
  toFun tv := ⟨((tv.2 : X × (ι → ℂ)).1, (((tv.1 : ℝ) : ℂ)) • (tv.2 : X × (ι → ℂ)).2),
    smul_mem_totalSet (tv.2).2 _⟩
  continuous_toFun :=
    ((continuous_fst.comp (continuous_subtype_val.comp continuous_snd)).prodMk
      ((Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)).smul
        (continuous_snd.comp (continuous_subtype_val.comp continuous_snd)))).subtype_mk _
  map_zero_left v := by
    apply Subtype.ext
    simp
  map_one_left v := by
    apply Subtype.ext
    simp

/-- **The total space of a bundle is homotopy equivalent to its base.** -/
def totalHomotopyEquivBase (p : Bundle X ι) : ContinuousMap.HomotopyEquiv (Total p) X where
  toFun := totalPi p
  invFun := zeroSection p
  left_inv := ⟨scaleHomotopy p⟩
  right_inv := by
    rw [totalPi_comp_zeroSection]

/-! ### `E(p) ∖ 0` retracts onto the sphere bundle -/

theorem retractCoeff_pos {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {s : ℝ} (hs : 0 < s) :
    0 < t + (1 - t) * s := by
  rcases le_total s 1 with h | h
  · nlinarith
  · nlinarith

theorem normalizeVec_mem_totalSet {p : Bundle X ι} {v : X × (ι → ℂ)} (hv : v ∈ totalSet p) :
    ((v.1, normalizeVec v.2) : X × (ι → ℂ)) ∈ totalSet p := by
  rw [normalizeVec_eq_smul]
  exact smul_mem_totalSet hv _

/-- The normalization map `E(p) ∖ 0 → S(p)`. -/
noncomputable def sphereRetract (p : Bundle X ι) : C(Punctured p, Sphere p) where
  toFun v := ⟨((v : X × (ι → ℂ)).1, normalizeVec (v : X × (ι → ℂ)).2),
    normalizeVec_mem_totalSet (v.2).1, normalizeVec_mem_unitVectors (v.2).2⟩
  continuous_toFun :=
    ((continuous_fst.comp continuous_subtype_val).prodMk
      (continuous_normalizeVec (continuous_snd.comp continuous_subtype_val)
        fun v => (v.2).2)).subtype_mk _

@[simp]
theorem sphereRetract_apply (p : Bundle X ι) (v : Punctured p) :
    (sphereRetract p v : X × (ι → ℂ))
      = ((v : X × (ι → ℂ)).1, normalizeVec (v : X × (ι → ℂ)).2) := rfl

theorem normalizeVec_of_mem_unitVectors {u : ι → ℂ} (hu : u ∈ unitVectors ι) :
    normalizeVec u = u := by
  rw [normalizeVec_eq_smul, mem_unitVectors_iff_eucNormSq.mp hu, Real.sqrt_one, inv_one,
    Complex.ofReal_one, one_smul]

theorem sphereRetract_comp_sphereToPunctured (p : Bundle X ι) :
    (sphereRetract p).comp (sphereToPunctured p) = ContinuousMap.id (Sphere p) := by
  apply ContinuousMap.ext
  intro v
  apply Subtype.ext
  show ((v : X × (ι → ℂ)).1, normalizeVec (v : X × (ι → ℂ)).2) = (v : X × (ι → ℂ))
  rw [normalizeVec_of_mem_unitVectors (v.2).2]

/-- The homotopy pushing `E(p) ∖ 0` onto its sphere bundle. -/
noncomputable def sphereHomotopy (p : Bundle X ι) :
    ContinuousMap.Homotopy ((sphereToPunctured p).comp (sphereRetract p))
      (ContinuousMap.id (Punctured p)) where
  toFun tv :=
    ⟨((tv.2 : X × (ι → ℂ)).1,
        (((tv.1 : ℝ) + (1 - (tv.1 : ℝ)) *
            (Real.sqrt (eucNormSq (tv.2 : X × (ι → ℂ)).2))⁻¹ : ℝ) : ℂ) •
          (tv.2 : X × (ι → ℂ)).2),
      smul_mem_totalSet (tv.2).2.1 _,
      smul_ne_zero_of_ne_zero
        (Complex.ofReal_ne_zero.mpr
          (ne_of_gt (retractCoeff_pos (tv.1).2.1 (tv.1).2.2
            (inv_pos.mpr (Real.sqrt_pos.mpr (eucNormSq_pos (tv.2).2.2))))))
        (tv.2).2.2⟩
  continuous_toFun := by
    have hsq : Continuous fun tv : I × Punctured p =>
        Real.sqrt (eucNormSq (tv.2 : X × (ι → ℂ)).2) :=
      Real.continuous_sqrt.comp
        (continuous_eucNormSq.comp (continuous_snd.comp (continuous_subtype_val.comp
          continuous_snd)))
    have hne : ∀ tv : I × Punctured p,
        Real.sqrt (eucNormSq (tv.2 : X × (ι → ℂ)).2) ≠ 0 :=
      fun tv => ne_of_gt (Real.sqrt_pos.mpr (eucNormSq_pos (tv.2).2.2))
    have ht : Continuous fun tv : I × Punctured p => ((tv.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hcoeff : Continuous fun tv : I × Punctured p =>
        ((tv.1 : ℝ) + (1 - (tv.1 : ℝ)) *
          (Real.sqrt (eucNormSq (tv.2 : X × (ι → ℂ)).2))⁻¹ : ℝ) :=
      ht.add ((continuous_const.sub ht).mul (hsq.inv₀ hne))
    exact (((continuous_fst.comp (continuous_subtype_val.comp continuous_snd)).prodMk
      ((Complex.continuous_ofReal.comp hcoeff).smul
        (continuous_snd.comp (continuous_subtype_val.comp continuous_snd)))).subtype_mk _)
  map_zero_left v := by
    apply Subtype.ext
    show ((v : X × (ι → ℂ)).1,
        (((((0 : I) : ℝ)) + (1 - (((0 : I) : ℝ))) *
          (Real.sqrt (eucNormSq (v : X × (ι → ℂ)).2))⁻¹ : ℝ) : ℂ) • (v : X × (ι → ℂ)).2)
      = ((v : X × (ι → ℂ)).1,
          (((Real.sqrt (eucNormSq (v : X × (ι → ℂ)).2))⁻¹ : ℝ) : ℂ) • (v : X × (ι → ℂ)).2)
    norm_num
  map_one_left v := by
    apply Subtype.ext
    show ((v : X × (ι → ℂ)).1,
        (((((1 : I) : ℝ)) + (1 - (((1 : I) : ℝ))) *
          (Real.sqrt (eucNormSq (v : X × (ι → ℂ)).2))⁻¹ : ℝ) : ℂ) • (v : X × (ι → ℂ)).2)
      = (v : X × (ι → ℂ))
    norm_num

/-- **The complement of the zero section is homotopy equivalent to the sphere
bundle.** -/
noncomputable def puncturedHomotopyEquivSphere (p : Bundle X ι) :
    ContinuousMap.HomotopyEquiv (Punctured p) (Sphere p) where
  toFun := sphereRetract p
  invFun := sphereToPunctured p
  left_inv := ⟨sphereHomotopy p⟩
  right_inv := by
    rw [sphereRetract_comp_sphereToPunctured]

end Scaling

end Bundle

end CharClass
end GroupApproximation
