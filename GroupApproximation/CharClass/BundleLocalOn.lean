import GroupApproximation.CharClass.BundleFrame

/-!
# Complex vector bundles in the projection model, XXVI: local triviality over a
subset of a trivialising set

A cover induction needs its predicate closed under intersection, so the chart
step has to hold over a trivialising set intersected with an arbitrary open, not
over `trivSet p x₀` itself.

**Shrinking is free**, and for a structural reason: `trivSet p x₀` is the
non-vanishing locus of `det (intert p x₀ ·)`, and the trivialisation is an
explicit formula in `intert`, not a choice of frame.  So every step of
`projTriv` needs only that the point lies in `trivSet p x₀`, and taking a subset
just composes the inclusion with that hypothesis.

What shrinking does **not** give is contractibility: an intersection of
trivialising sets with arbitrary opens stays trivialising and stops being
contractible.  A chart step must therefore be stated over an arbitrary
trivialising open, never over a contractible one.

## Manuscript status

Machinery.  Certifies no manuscript step on its own.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open scoped Matrix
open GroupApproximation.STW59

namespace Bundle

section LocalOn

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem projTrivOn_invFun_mem (p : Bundle X ι) (x₀ : X) (V : Set X) (hV : V ⊆ trivSet p x₀)
    (z : ↥V × ↥(projFibreSet (p x₀))) :
    (z.1, conjNormalize (intert p x₀ (z.1 : X))⁻¹ (z.2 : Matrix ι ι ℂ)) ∈
      projSet (p.restrictTo V) :=
  conjNormalize_mem_projFibreSet (isUnit_det_inv_intert (hV z.1.2))
    (inv_intert_mul (hV z.1.2)) z.2.2

/-- **Local triviality of the projective bundle over any subset of a
trivialising set.**  `projTriv` is the case `V = trivSet p x₀`. -/
noncomputable def projTrivOn (p : Bundle X ι) (x₀ : X) (V : Set X) (hV : V ⊆ trivSet p x₀) :
    Proj (p.restrictTo V) ≃ₜ ↥V × ↥(projFibreSet (p x₀)) where
  toFun z := ((z : ↥V × Matrix ι ι ℂ).1,
    ⟨conjNormalize (intert p x₀ ((z : ↥V × Matrix ι ι ℂ).1 : X))
      (z : ↥V × Matrix ι ι ℂ).2,
      conjNormalize_mem_projFibreSet
        (isUnit_det_intert (hV (z : ↥V × Matrix ι ι ℂ).1.2))
        (intert_mul p x₀ _) z.2⟩)
  invFun z := ⟨(z.1, conjNormalize (intert p x₀ (z.1 : X))⁻¹ (z.2 : Matrix ι ι ℂ)),
    projTrivOn_invFun_mem p x₀ V hV z⟩
  left_inv z := by
    apply Subtype.ext
    refine Prod.ext rfl ?_
    exact conjNormalize_conjNormalize
      (isUnit_det_intert (hV (z : ↥V × Matrix ι ι ℂ).1.2)) z.2
  right_inv z := by
    refine Prod.ext rfl ?_
    apply Subtype.ext
    have hinv : ((intert p x₀ (z.1 : X))⁻¹)⁻¹ = intert p x₀ (z.1 : X) :=
      Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_intert (hV z.1.2))
    have h := conjNormalize_conjNormalize (a := (intert p x₀ (z.1 : X))⁻¹)
      (isUnit_det_inv_intert (hV z.1.2)) z.2.2
    rwa [hinv] at h
  continuous_toFun :=
    (continuous_fst.comp continuous_subtype_val).prodMk
      ((continuous_conjNormalize
        ((continuous_intert p x₀).comp
          (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)))
        (continuous_snd.comp continuous_subtype_val)
        (fun z => by
          obtain ⟨u, hu, hru, -⟩ := exists_unitVector_of_mem_projFibreSet z.2
          simp only [Function.comp_apply, hru]
          exact (trace_conj_ne_zero_iff _ _).mpr
            (mulVec_ne_zero_of_isUnit
              (isUnit_det_intert (hV (z : ↥V × Matrix ι ι ℂ).1.2))
              (ne_zero_of_eucNormSq_eq_one hu)))).subtype_mk _)
  continuous_invFun :=
    (continuous_fst.prodMk
      (continuous_conjNormalize
        (((continuous_inv_intert p x₀).comp (continuous_inclusion hV)).comp continuous_fst)
        (continuous_subtype_val.comp continuous_snd)
        (fun z => by
          obtain ⟨u, hu, hru, -⟩ := exists_unitVector_of_mem_projFibreSet z.2.2
          simp only [Function.comp_apply, hru]
          exact (trace_conj_ne_zero_iff _ _).mpr
            (mulVec_ne_zero_of_isUnit (isUnit_det_inv_intert (hV z.1.2))
              (ne_zero_of_eucNormSq_eq_one hu))))).subtype_mk _

theorem projTrivOn_over_base (p : Bundle X ι) (x₀ : X) (V : Set X) (hV : V ⊆ trivSet p x₀)
    (z : Proj (p.restrictTo V)) :
    (projTrivOn p x₀ V hV z).1 = projPi (p.restrictTo V) z := rfl

end LocalOn

end Bundle

/-- **`P(p)` is literally `V × ℂP^d` over any subset of a trivialising set.**
The shape a cover induction consumes, since its predicate must be closed under
intersection with an arbitrary open. -/
noncomputable def Bundle.projTrivStdOn {X : Type} [TopologicalSpace X] {ι : Type}
    [Fintype ι] [DecidableEq ι] (p : Bundle X ι) (x₀ : X) (V : Set X)
    (hV : V ⊆ Bundle.trivSet p x₀) (d : ℕ) (hr : p.rank x₀ = d + 1) :
    Bundle.Proj (p.restrictTo V) ≃ₜ ↥V × CP d :=
  (Bundle.projTrivOn p x₀ V hV).trans
    (Homeomorph.prodCongr (Homeomorph.refl _)
      (projFibreEquivCP (p.isStarProjection x₀) d (by rw [Bundle.trace_eq_rank, hr])))

theorem Bundle.projTrivStdOn_over_base {X : Type} [TopologicalSpace X] {ι : Type}
    [Fintype ι] [DecidableEq ι] (p : Bundle X ι) (x₀ : X) (V : Set X)
    (hV : V ⊆ Bundle.trivSet p x₀) (d : ℕ) (hr : p.rank x₀ = d + 1)
    (z : Bundle.Proj (p.restrictTo V)) :
    (Bundle.projTrivStdOn p x₀ V hV d hr z).1 = Bundle.projPi (p.restrictTo V) z := rfl

end CharClass
end GroupApproximation
