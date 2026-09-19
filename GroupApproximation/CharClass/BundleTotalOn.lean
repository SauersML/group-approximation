import GroupApproximation.CharClass.BundlePairs

/-!
# Complex vector bundles in the projection model, XXX: the total space over a
subset of a trivialising set

`BundleLocalOn` shrinks the **projective** trivialisation to any subset of a
trivialising set.  A Thom argument needs the **total-space** one shrunk the same
way, for the same reason and with a sharper edge: a pair identification pinned to
`trivSet p x₀` cannot be fed to a corollary that wants a contractible base,
because `trivSet` is a determinant non-vanishing locus and carries no
contractibility.  Shrinking lets a consumer intersect with a chart and take a
ball inside.

Shrinking is again just threading `hV`: the trivialisation is an explicit
formula in `intert`, so every step needs only that the point lies in
`trivSet p x₀`.

The pair statement is an **image equation**, matching `totalTrivStd_image_punctured`,
because that is the form a relative-cohomology congruence consumes.

## Manuscript status

Machinery.  Certifies no manuscript step on its own.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open scoped Matrix
open GroupApproximation.STW59

namespace Bundle

section TotalOn

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem totalTrivOn_toFun_mem (p : Bundle X ι) (x₀ : X) (V : Set X)
    (w : Total (p.restrictTo V)) :
    intert p x₀ ((w : ↥V × (ι → ℂ)).1 : X) *ᵥ (w : ↥V × (ι → ℂ)).2 ∈ fibreSet (p x₀) := by
  show p x₀ *ᵥ (intert p x₀ _ *ᵥ _) = intert p x₀ _ *ᵥ _
  have hw := mem_totalSet_iff.mp w.2
  rw [restrictTo_apply] at hw
  rw [Matrix.mulVec_mulVec, ← intert_mul, ← Matrix.mulVec_mulVec, hw]

theorem totalTrivOn_invFun_mem (p : Bundle X ι) (x₀ : X) (V : Set X)
    (hV : V ⊆ trivSet p x₀) (w : ↥V × ↥(fibreSet (p x₀))) :
    (w.1, (intert p x₀ (w.1 : X))⁻¹ *ᵥ (w.2 : ι → ℂ)) ∈ totalSet (p.restrictTo V) := by
  show p (w.1 : X) *ᵥ ((intert p x₀ (w.1 : X))⁻¹ *ᵥ (w.2 : ι → ℂ))
    = (intert p x₀ (w.1 : X))⁻¹ *ᵥ (w.2 : ι → ℂ)
  rw [Matrix.mulVec_mulVec, ← inv_intert_mul (hV w.1.2), ← Matrix.mulVec_mulVec, w.2.2]

/-- **Local triviality of the total space over any subset of a trivialising
set.**  `totalTriv` is the case `V = trivSet p x₀`. -/
noncomputable def totalTrivOn (p : Bundle X ι) (x₀ : X) (V : Set X) (hV : V ⊆ trivSet p x₀) :
    Total (p.restrictTo V) ≃ₜ ↥V × ↥(fibreSet (p x₀)) where
  toFun w := ((w : ↥V × (ι → ℂ)).1,
    ⟨intert p x₀ ((w : ↥V × (ι → ℂ)).1 : X) *ᵥ (w : ↥V × (ι → ℂ)).2,
      totalTrivOn_toFun_mem p x₀ V w⟩)
  invFun w := ⟨(w.1, (intert p x₀ (w.1 : X))⁻¹ *ᵥ (w.2 : ι → ℂ)),
    totalTrivOn_invFun_mem p x₀ V hV w⟩
  left_inv w := by
    apply Subtype.ext
    refine Prod.ext rfl ?_
    show (intert p x₀ ((w : ↥V × (ι → ℂ)).1 : X))⁻¹
        *ᵥ (intert p x₀ ((w : ↥V × (ι → ℂ)).1 : X) *ᵥ (w : ↥V × (ι → ℂ)).2)
      = (w : ↥V × (ι → ℂ)).2
    rw [Matrix.mulVec_mulVec, inv_mul_intert (hV (w : ↥V × (ι → ℂ)).1.2), Matrix.one_mulVec]
  right_inv w := by
    refine Prod.ext rfl ?_
    apply Subtype.ext
    show intert p x₀ (w.1 : X) *ᵥ ((intert p x₀ (w.1 : X))⁻¹ *ᵥ (w.2 : ι → ℂ))
      = (w.2 : ι → ℂ)
    rw [Matrix.mulVec_mulVec, intert_mul_inv (hV w.1.2), Matrix.one_mulVec]
  continuous_toFun :=
    (continuous_fst.comp continuous_subtype_val).prodMk
      ((((continuous_intert p x₀).comp
        (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val))).matrix_mulVec
        (continuous_snd.comp continuous_subtype_val)).subtype_mk _)
  continuous_invFun :=
    ((continuous_fst.prodMk
      ((((continuous_inv_intert p x₀).comp (continuous_inclusion hV)).comp
        continuous_fst).matrix_mulVec
        (continuous_subtype_val.comp continuous_snd)))).subtype_mk _

theorem totalTrivOn_over_base (p : Bundle X ι) (x₀ : X) (V : Set X) (hV : V ⊆ trivSet p x₀)
    (w : Total (p.restrictTo V)) :
    (totalTrivOn p x₀ V hV w).1 = totalPi (p.restrictTo V) w := rfl

end TotalOn

end Bundle

/-- **`E(p)` is literally `V × ℂ^r` over any subset of a trivialising set.** -/
noncomputable def Bundle.totalTrivStdOn {X : Type} [TopologicalSpace X] {ι : Type}
    [Fintype ι] [DecidableEq ι] (p : Bundle X ι) (x₀ : X) (V : Set X)
    (hV : V ⊆ Bundle.trivSet p x₀) (r : ℕ) (hr : p.rank x₀ = r) :
    Bundle.Total (p.restrictTo V) ≃ₜ ↥V × (Fin r → ℂ) :=
  (Bundle.totalTrivOn p x₀ V hV).trans
    (Homeomorph.prodCongr (Homeomorph.refl _)
      (fibreEquivPi (p.isStarProjection x₀) r (by rw [Bundle.trace_eq_rank, hr])))

theorem Bundle.totalTrivStdOn_over_base {X : Type} [TopologicalSpace X] {ι : Type}
    [Fintype ι] [DecidableEq ι] (p : Bundle X ι) (x₀ : X) (V : Set X)
    (hV : V ⊆ Bundle.trivSet p x₀) (r : ℕ) (hr : p.rank x₀ = r)
    (w : Bundle.Total (p.restrictTo V)) :
    (Bundle.totalTrivStdOn p x₀ V hV r hr w).1 = Bundle.totalPi (p.restrictTo V) w := rfl

namespace Bundle

section TotalOnPair

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem totalTrivStdOn_snd_eq_zero_iff (p : Bundle X ι) (x₀ : X) (V : Set X)
    (hV : V ⊆ trivSet p x₀) (r : ℕ) (hr : p.rank x₀ = r) (w : Total (p.restrictTo V)) :
    (Bundle.totalTrivStdOn p x₀ V hV r hr w).2 = 0
      ↔ (w : ↥V × (ι → ℂ)).2 = 0 := by
  have hq : (p x₀).trace = (r : ℂ) := by rw [trace_eq_rank, hr]
  have hval : (Bundle.totalTrivStdOn p x₀ V hV r hr w).2
      = fibreEquivPi (p.isStarProjection x₀) r hq ((totalTrivOn p x₀ V hV w).2) := rfl
  rw [hval, fibreEquivPi_eq_zero_iff]
  constructor
  · intro h
    have h2 : intert p x₀ ((w : ↥V × (ι → ℂ)).1 : X) *ᵥ (w : ↥V × (ι → ℂ)).2 = 0 := h
    by_contra hne
    exact mulVec_ne_zero_of_isUnit
      (isUnit_det_intert (hV (w : ↥V × (ι → ℂ)).1.2)) hne h2
  · intro h
    show intert p x₀ ((w : ↥V × (ι → ℂ)).1 : X) *ᵥ (w : ↥V × (ι → ℂ)).2 = 0
    rw [h, Matrix.mulVec_zero]

/-- **The trivialisation over `V` as a map of pairs**, in the image form a
relative-cohomology congruence consumes. -/
theorem totalTrivStdOn_image_punctured (p : Bundle X ι) (x₀ : X) (V : Set X)
    (hV : V ⊆ trivSet p x₀) (r : ℕ) (hr : p.rank x₀ = r) :
    (Bundle.totalTrivStdOn p x₀ V hV r hr) ''
        {w : Total (p.restrictTo V) |
          (w : ↥V × (ι → ℂ)) ∈ puncturedSet (p.restrictTo V)}
      = {q : ↥V × (Fin r → ℂ) | q.2 ≠ 0} := by
  ext q
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact fun h => hw.2 ((totalTrivStdOn_snd_eq_zero_iff p x₀ V hV r hr w).mp h)
  · intro hq
    refine ⟨(Bundle.totalTrivStdOn p x₀ V hV r hr).symm q,
      ⟨((Bundle.totalTrivStdOn p x₀ V hV r hr).symm q).2, ?_⟩,
      (Bundle.totalTrivStdOn p x₀ V hV r hr).apply_symm_apply q⟩
    intro h
    refine hq ?_
    rw [← (Bundle.totalTrivStdOn p x₀ V hV r hr).apply_symm_apply q]
    exact (totalTrivStdOn_snd_eq_zero_iff p x₀ V hV r hr _).mpr h

end TotalOnPair

end Bundle

end CharClass
end GroupApproximation
