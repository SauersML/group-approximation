import GroupApproximation.CharClass.BundleGysinPieces
import GroupApproximation.CharClass.BundleReindex

/-!
# Complex vector bundles in the projection model, XXIII: two facts a Gysin datum
needs

**The chart's equivalence to the base is the projection.**  `chartOpensHomotopyEquivBase`
is assembled from three homeomorphisms and a scaling homotopy, and none of them
moves the base point, so its forward map is the bundle projection restricted --
on the nose, not up to homotopy.  A Gysin datum needs that to know the chart's
retraction is a section of the projection.

**The sphere bundle of the tautological line over `ℂP^d` is the odd sphere.**
A point of it is a point of `ℂP^d` together with a unit vector of that line, and
the line is recovered from the vector, so the second coordinate alone is a
homeomorphism onto the unit sphere of the ambient `ℂ^{d+1}`.  This is what makes
an acyclicity hypothesis discharge against odd-sphere vanishing.

Note the second is special to the tautological line.  The sphere bundle of a
general line bundle is a circle bundle, not a sphere.

## Manuscript status

Machinery.  Certifies no manuscript step on its own.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open scoped Matrix
open GroupApproximation.STW59

namespace Bundle

/-! ### The chart's equivalence to the base is the projection -/

section ChartProjection

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **The forward map of `chartOpensHomotopyEquivBase` is the bundle
projection**, restricted to the chart.  By `rfl`. -/
theorem chartOpensHomotopyEquivBase_toFun_apply (p : Bundle X ι)
    (z : ↥(chartOpensSet p)) :
    (chartOpensHomotopyEquivBase p).toFun z = projPi p.plusOne (z : Proj p.plusOne) := rfl

end ChartProjection

/-! ### The sphere bundle of the tautological line -/

section TautSphere

variable {d : ℕ}

theorem rankOneProj_mem_cpSet {u : Fin (d + 1) → ℂ} (hu : u ∈ unitVectors (Fin (d + 1))) :
    rankOneProj u ∈ cpSet d :=
  ⟨(isStarProjection_matrix_iff.mp (isStarProjection_rankOneProj hu)).1,
    (isStarProjection_matrix_iff.mp (isStarProjection_rankOneProj hu)).2,
    trace_rankOneProj hu⟩

theorem sphereCpTaut_mem {u : Fin (d + 1) → ℂ} (hu : u ∈ unitVectors (Fin (d + 1))) :
    ((⟨rankOneProj u, rankOneProj_mem_cpSet hu⟩ : CP d), u) ∈ sphereSet (cpTaut d) :=
  ⟨rankOneProj_mulVec_self hu, hu⟩

/-- **The sphere bundle of the tautological line over `ℂP^d` is the unit sphere
of `ℂ^{d+1}`**, that is, `S^{2d+1}`.  The line is recovered from the vector, so
the second coordinate alone is the homeomorphism. -/
noncomputable def sphereCpTautHomeo (d : ℕ) :
    Sphere (cpTaut d) ≃ₜ ↥(unitVectors (Fin (d + 1))) where
  toFun w := ⟨(w : CP d × (Fin (d + 1) → ℂ)).2, w.2.2⟩
  invFun u := ⟨((⟨rankOneProj (u : Fin (d + 1) → ℂ), rankOneProj_mem_cpSet u.2⟩ : CP d),
    (u : Fin (d + 1) → ℂ)), sphereCpTaut_mem u.2⟩
  left_inv w := by
    apply Subtype.ext
    refine Prod.ext ?_ rfl
    apply Subtype.ext
    have hv : (w : CP d × (Fin (d + 1) → ℂ)).2 ≠ 0 :=
      ne_zero_of_eucNormSq_eq_one w.2.2
    have hfix : ((w : CP d × (Fin (d + 1) → ℂ)).1
        : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) *ᵥ (w : CP d × (Fin (d + 1) → ℂ)).2
        = (w : CP d × (Fin (d + 1) → ℂ)).2 := w.2.1
    have hline : lineOf (w : CP d × (Fin (d + 1) → ℂ)).2
        = ((w : CP d × (Fin (d + 1) → ℂ)).1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :=
      lineOf_eq_of_mem_fibre (isStarProjection_taut d _)
        (trace_taut d _) hv hfix
    rw [← hline, lineOf_of_mem_unitVectors w.2.2]
  right_inv _ := rfl
  continuous_toFun := (continuous_snd.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    (((continuous_rankOneProj'.comp continuous_subtype_val).subtype_mk _).prodMk
      continuous_subtype_val).subtype_mk _

/-- The homeomorphism is the second coordinate. -/
theorem sphereCpTautHomeo_apply (d : ℕ) (w : Sphere (cpTaut d)) :
    (sphereCpTautHomeo d w : Fin (d + 1) → ℂ) = (w : CP d × (Fin (d + 1) → ℂ)).2 := rfl

end TautSphere

end Bundle

end CharClass
end GroupApproximation
