import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketLakeAbsorption
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P06, lake-free face sets: monotonicity of the exterior piece

Infrastructure for lane gl-p06-05 (Route B of `carto-gl-p06`), Osin, arXiv:math/0411039v3, §9,
proof of Lemma 9.7(b): the subdiagram `Γ_1` between two regions joining the same cells.

`ExteriorComponent.component M faces o` is the piece of `o`: faces reached from `o` by moving
around faces and crossing edges off the boundary of `faces` (`OsinPocketLakeAbsorption.lean`).

## Truth check and proof

* *Shrinking the face set grows the piece of an outside face.*  Let `faces' ⊆ faces` and
  `o ∉ faces`.  Every dart on a reach from `o` lies on a face outside `faces`
  (`faceOf_mem_iff_of_eqvGen`).  A crossing of the edge of `x` off the boundary of `faces`, with
  `faceOf x ∉ faces`, is also off the boundary of `faces'`: a boundary dart `x` of `faces'` has
  `faceOf x ∈ faces' ⊆ faces`, impossible; a boundary dart `α x` of `faces'` has
  `faceOf (α x) ∈ faces` and `faceOf (α (α x)) = faceOf x ∉ faces`, so `α x` is a boundary dart of
  `faces`, against the crossing being allowed.  Induction on the equivalence closure (the invariant
  `faceOf x ∉ faces` passes along each step by `faceOf_mem_iff_of_eqvGen`).
* *A face touching the old piece joins the new piece.*  If `faceOf d ∉ faces'` and
  `faceOf (α d)` lies in the piece of `o` for `faces`, then `faceOf (α d)` lies in the piece for
  `faces'` by monotonicity, hence off `faces'`, so neither `α d` nor `α (α d) = d` is a boundary
  dart of `faces'`; `Reach.alpha` crosses into `d`.
* *No lakes means nothing to fill.*  If every face off `faces` lies in the piece of `o ∉ faces`,
  then `absorbed M faces o = faces`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree

universe v

open Surgery.MapCollapse Surgery.MapCollapse.ExteriorComponent

variable {M : CombMap.{v}}

/-- **Reaches off a face set are reaches off every smaller face set**, as long as they start on a
face outside the larger face set. -/
theorem eqvGen_mono_of_not_mem {faces faces' : Finset M.Face} (hsub : faces' ⊆ faces)
    {x y : M.Dart}
    (h : Relation.EqvGen (CombMap.FaceClassStep M (BoundaryEdge M faces)) x y) :
    M.faceOf x ∉ faces →
      Relation.EqvGen (CombMap.FaceClassStep M (BoundaryEdge M faces')) x y := by
  induction h with
  | rel x₁ x₂ hx =>
      intro hx₁
      rcases hx with hstep | ⟨hoff, hstep⟩
      · exact Relation.EqvGen.rel _ _
          (show CombMap.FaceClassStep M (BoundaryEdge M faces') x₁ x₂ from Or.inl hstep)
      · refine Relation.EqvGen.rel _ _
          (show CombMap.FaceClassStep M (BoundaryEdge M faces') x₁ x₂ from Or.inr ⟨?_, hstep⟩)
        rintro (hb | hb)
        · obtain ⟨hin, -⟩ := hb
          exact hx₁ (hsub hin)
        · obtain ⟨hin, -⟩ := hb
          have hback : M.faceOf (M.alpha (M.alpha x₁)) ∉ faces := by
            rw [M.alpha_involutive x₁]
            exact hx₁
          exact hoff (show IsBoundaryDart M faces x₁ ∨ IsBoundaryDart M faces (M.alpha x₁) from
            Or.inr (show M.faceOf (M.alpha x₁) ∈ faces ∧
              M.faceOf (M.alpha (M.alpha x₁)) ∉ faces from ⟨hsub hin, hback⟩))
  | refl x₁ =>
      intro _
      exact Relation.EqvGen.refl x₁
  | symm x₁ x₂ h₁ ih =>
      intro hx₂
      have hx₁ : M.faceOf x₁ ∉ faces := fun hin => hx₂ ((faceOf_mem_iff_of_eqvGen h₁).mp hin)
      exact Relation.EqvGen.symm _ _ (ih hx₁)
  | trans x₁ x₂ _ h₁ _ ih₁ ih₂ =>
      intro hx₁
      have hx₂ : M.faceOf x₂ ∉ faces := fun hin => hx₁ ((faceOf_mem_iff_of_eqvGen h₁).mpr hin)
      exact Relation.EqvGen.trans _ _ _ (ih₁ hx₁) (ih₂ hx₂)

/-- **Shrinking the face set grows the piece of an outside face.** -/
theorem component_subset_of_subset {faces faces' : Finset M.Face} (hsub : faces' ⊆ faces)
    {o : M.Face} (ho : o ∉ faces) :
    ExteriorComponent.component M faces o ⊆ ExteriorComponent.component M faces' o := by
  intro f hf
  obtain ⟨y, hy, x, hx, hxy⟩ := mem_component_iff.mp hf
  have hx' : M.faceOf x ∉ faces := by
    rw [hx]
    exact ho
  exact mem_component_iff.mpr ⟨y, hy, x, hx, eqvGen_mono_of_not_mem hsub hxy hx'⟩

/-- **A face off the smaller face set touching the old piece joins the new piece.** -/
theorem mem_component_of_touch {faces faces' : Finset M.Face} (hsub : faces' ⊆ faces)
    {o : M.Face} (ho : o ∉ faces) {d : M.Dart} (hd : M.faceOf d ∉ faces')
    (hα : M.faceOf (M.alpha d) ∈ ExteriorComponent.component M faces o) :
    M.faceOf d ∈ ExteriorComponent.component M faces' o := by
  have hα' : M.faceOf (M.alpha d) ∈ ExteriorComponent.component M faces' o :=
    component_subset_of_subset hsub ho hα
  have ho' : o ∉ faces' := fun h => ho (hsub h)
  obtain ⟨y, hy, hreach⟩ := mem_component_iff.mp hα'
  have hoff : ¬ BoundaryEdge M faces' (M.alpha d) := by
    rintro (hb | hb)
    · obtain ⟨hin, -⟩ := hb
      exact not_mem_of_mem_component ho' hα' hin
    · obtain ⟨hin, -⟩ := hb
      rw [M.alpha_involutive d] at hin
      exact hd hin
  have hd' := (hreach.of_faceOf_eq hy).alpha hoff
  rw [M.alpha_involutive d] at hd'
  exact mem_component_iff.mpr ⟨d, rfl, hd'⟩

/-- **No lakes means nothing to fill**: when every face off the face set lies in the piece of an
outside face `o`, filling the lakes keeps the face set. -/
theorem absorbed_eq_of_forall_mem_component {faces : Finset M.Face} {o : M.Face}
    (ho : o ∉ faces) (h : ∀ f, f ∉ faces → f ∈ ExteriorComponent.component M faces o) :
    ExteriorComponent.absorbed M faces o = faces := by
  ext f
  rw [mem_absorbed_iff]
  constructor
  · intro hf
    by_contra hout
    exact hf (h f hout)
  · intro hf hc
    exact not_mem_of_mem_component ho hc hf

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.eqvGen_mono_of_not_mem
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.component_subset_of_subset
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.mem_component_of_touch
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.absorbed_eq_of_forall_mem_component
