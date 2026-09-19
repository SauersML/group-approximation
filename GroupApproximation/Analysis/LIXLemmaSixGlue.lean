import GroupApproximation.Analysis.LIXLemmaSixShape

/-!
# Gluing the two hemisphere frames over `S⁵`

Corollary 4 compares the twisted bundle with the untwisted one by gluing:
the northern frame on the northern cap, and on the southern cap the southern
frame corrected by the contraction of a null-homotopy.  This file supplies the
gluing itself, which is where the topology of the sphere enters and the only
place it does.

The two caps are `{Re (x 2) ≥ 0}` and `{Re (x 2) ≤ 0}`.  They are closed, they
cover, and they meet in the equator `{Re (x 2) = 0}`, which is exactly the
hypothesis shape of Mathlib's `continuous_if_le`: the northern frame is
continuous on the northern cap because `Re (x 2) ≥ 0` already forces
`x 2 ≠ -1`, and symmetrically on the south, so no separate estimate near the
seam is needed.
-/

namespace GroupApproximation
namespace LIX

open scoped Matrix ComplexOrder CStarAlgebra

set_option linter.unusedSectionVars false

noncomputable section

/-- The northern cap of `S⁵` for the chart with pole `e₃`. -/
def northCap : Set ↥STW59.sphereFive := {x | 0 ≤ ((x : Fin 3 → ℂ) 2).re}

/-- The southern cap. -/
def southCap : Set ↥STW59.sphereFive := {x | ((x : Fin 3 → ℂ) 2).re ≤ 0}

theorem mem_northCap_iff (x : ↥STW59.sphereFive) :
    x ∈ northCap ↔ 0 ≤ ((x : Fin 3 → ℂ) 2).re := Iff.rfl

theorem mem_southCap_iff (x : ↥STW59.sphereFive) :
    x ∈ southCap ↔ ((x : Fin 3 → ℂ) 2).re ≤ 0 := Iff.rfl

/-- On the northern cap the southern pole is excluded, which is exactly the
condition the northern frame needs. -/
theorem ne_neg_one_of_mem_northCap {x : ↥STW59.sphereFive} (hx : x ∈ northCap) :
    (x : Fin 3 → ℂ) 2 ≠ -1 := by
  intro hc
  rw [mem_northCap_iff, hc] at hx
  norm_num at hx

theorem ne_one_of_mem_southCap {x : ↥STW59.sphereFive} (hx : x ∈ southCap) :
    (x : Fin 3 → ℂ) 2 ≠ 1 := by
  intro hc
  rw [mem_southCap_iff, hc] at hx
  norm_num at hx

theorem continuous_capHeight :
    Continuous fun x : ↥STW59.sphereFive => ((x : Fin 3 → ℂ) 2).re :=
  Complex.continuous_re.comp ((continuous_apply 2).comp continuous_subtype_val)

theorem continuousOn_frameRot_northCap :
    ContinuousOn (fun x : ↥STW59.sphereFive => frameRot e3 (x : Fin 3 → ℂ)) northCap := by
  rw [continuousOn_iff_continuous_restrict]
  exact continuous_frameRot continuous_const
    (continuous_subtype_val.comp continuous_subtype_val)
    (fun s => isFrameDatum_e3 s.1.2 (ne_neg_one_of_mem_northCap s.2))

theorem continuousOn_frameRot_southCap :
    ContinuousOn (fun x : ↥STW59.sphereFive => frameRot (-e3) (x : Fin 3 → ℂ)) southCap := by
  rw [continuousOn_iff_continuous_restrict]
  exact continuous_frameRot continuous_const
    (continuous_subtype_val.comp continuous_subtype_val)
    (fun s => isFrameDatum_neg_e3 s.1.2 (ne_one_of_mem_southCap s.2))

/-- **The gluing.**  A field defined on the southern cap that agrees with the
northern frame on the equator extends the northern frame to a continuous field
on all of `S⁵`.  The frontier condition of `continuous_if_le` is discharged by
the equator, so nothing has to be proved about limits at the seam. -/
theorem continuous_capGlue {ι : Type*} [TopologicalSpace ι]
    {F G : ↥STW59.sphereFive → ι}
    (hF : ContinuousOn F northCap) (hG : ContinuousOn G southCap)
    (hseam : ∀ x : ↥STW59.sphereFive, ((x : Fin 3 → ℂ) 2).re = 0 → F x = G x) :
    Continuous fun x : ↥STW59.sphereFive =>
      if 0 ≤ ((x : Fin 3 → ℂ) 2).re then F x else G x :=
  continuous_if_le continuous_const continuous_capHeight hF hG
    fun x hx => hseam x hx.symm

/-- The glued field agrees with `F` on the northern cap. -/
theorem capGlue_of_mem_northCap {ι : Type*} {F G : ↥STW59.sphereFive → ι}
    {x : ↥STW59.sphereFive} (hx : x ∈ northCap) :
    (if 0 ≤ ((x : Fin 3 → ℂ) 2).re then F x else G x) = F x :=
  if_pos hx

/-- Off the northern cap the glued field is `G`. -/
theorem capGlue_of_not_mem_northCap {ι : Type*} {F G : ↥STW59.sphereFive → ι}
    {x : ↥STW59.sphereFive} (hx : x ∉ northCap) :
    (if 0 ≤ ((x : Fin 3 → ℂ) 2).re then F x else G x) = G x :=
  if_neg hx

/-- The two caps cover the sphere. -/
theorem northCap_union_southCap : northCap ∪ southCap = Set.univ := by
  ext x
  simp only [Set.mem_union, mem_northCap_iff, mem_southCap_iff, Set.mem_univ, iff_true]
  exact le_total 0 _

/-- Their intersection is the equator. -/
theorem mem_northCap_inter_southCap_iff (x : ↥STW59.sphereFive) :
    x ∈ northCap ∩ southCap ↔ ((x : Fin 3 → ℂ) 2).re = 0 := by
  simp only [Set.mem_inter_iff, mem_northCap_iff, mem_southCap_iff]
  exact ⟨fun h => le_antisymm h.2 h.1, fun h => ⟨h.ge, h.le⟩⟩

end

end LIX
end GroupApproximation
