import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellFaceSet
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketLakeAbsorption
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.DefComponent
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P06, Route B: lake-free cell pocket face sets

Lane gl-p06-05 of `carto-gl-p06`.  Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b):

> "Let us consider the subdiagram `Γ_1` of `Δ` such that: (i) `∂Γ_1 = s_1 t_1 s_2 t_2`, where
> `s_1, s_2` are side arcs of some of `Γ_{i,1}`'s and `t_1, t_2` are subpaths of `∂Π` and the
> section `q_1` of `∂Δ`, respectively; (ii) `Γ_1` contains all `Γ_{i,1}`'s."

A cell pocket face set `K` (`CellPocketFaceSet`, `Estimating/OsinPocketCellFaceSet.lean`) is
*lake free* when every face off `K.faces` lies in the exterior piece `E₀`, the piece of the outer
face reached by moving around faces and crossing edges off the boundary of `K.faces`
(`ExteriorComponent.component`).  This is the hypothesis of the corrected Piece06 face-set statement
(Route B, lane gl-p06-07), which rules out case (d) of `CellRoseLakesSurgeryBelowStatement`.

## Truth check and proof

* `cell_mem_component_of_lakeFree`: `Π_i` and `Π_j` are off `K.faces` (`first_not_mem`,
  `second_not_mem`), so a lake-free `K` puts them in `E₀`.  True by definition.
* `absorbed_eq_of_lakeFree`, `isBoundaryDart_absorbed_iff_of_lakeFree`: filling the lakes of a
  lake-free face set changes nothing, since `absorbed = univ ∖ E₀ = K.faces`
  (`absorbed_eq_of_forall_mem_component`, using `K.outerFace_not_mem`).
* `lakeFree_of_boundary_subset`: let `K'` be a cell pocket face set (any cells, any bound) with
  `K'.faces ⊆ K.faces`, each removed face `f ∈ K.faces ∖ K'.faces` having a dart `d` whose
  reversal faces `E₀`.  Take `f ∉ K'.faces`.  If `f ∉ K.faces`, then `f ∈ E₀` by lake freeness,
  and `E₀` grows when the face set shrinks (`component_subset_of_subset`).  Otherwise `f` is a
  removed face and `mem_component_of_touch` crosses from `faceOf (α d) ∈ E₀` into `f`.  Small
  model: two faces `a, b` inside, `b` adjacent to the exterior; removing `b` leaves `{a}`, whose
  exterior piece contains `b` and every old exterior face.  Removing `a` alone, with `a` adjacent
  only to `b`, violates the touching hypothesis, and indeed `a` would be a lake of `{b}`.
* `lakeFree_of_boundary_cycle`: the touching hypothesis holds when each removed face carries a
  dart of the boundary cycle of `K` (its reversal faces off `K.faces`, hence `E₀`).

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree

universe u w v

open Embedded HullSC WordMetric Surgery.MapCollapse Surgery.MapCollapse.ExteriorComponent

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **A lake-free cell pocket face set**: every face off the face set lies in the exterior piece,
the piece of the outer face reached without crossing the boundary of the face set. -/
def CellPocketLakeFree (K : CellPocketFaceSet D eps X i j) : Prop :=
  ∀ f, f ∉ K.faces → f ∈ ExteriorComponent.component X.toCombMap K.faces X.outerFace

/-- **Both cells face the exterior piece** of a lake-free cell pocket face set. -/
theorem cell_mem_component_of_lakeFree {K : CellPocketFaceSet D eps X i j}
    (hK : CellPocketLakeFree K) :
    (cell X i).face ∈ ExteriorComponent.component X.toCombMap K.faces X.outerFace ∧
      (cell X j).face ∈ ExteriorComponent.component X.toCombMap K.faces X.outerFace :=
  ⟨hK _ K.first_not_mem, hK _ K.second_not_mem⟩

/-- In a lake-free cell pocket face set, the exterior piece is exactly the complement. -/
theorem mem_component_iff_of_lakeFree {K : CellPocketFaceSet D eps X i j}
    (hK : CellPocketLakeFree K) (f : X.toCombMap.Face) :
    f ∈ ExteriorComponent.component X.toCombMap K.faces X.outerFace ↔ f ∉ K.faces :=
  ⟨fun hc => not_mem_of_mem_component K.outerFace_not_mem hc, hK f⟩

/-- **Filling the lakes of a lake-free cell pocket face set keeps its faces.** -/
theorem absorbed_eq_of_lakeFree {K : CellPocketFaceSet D eps X i j}
    (hK : CellPocketLakeFree K) :
    ExteriorComponent.absorbed X.toCombMap K.faces X.outerFace = K.faces :=
  absorbed_eq_of_forall_mem_component K.outerFace_not_mem hK

/-- **The boundary darts after filling the lakes are the old boundary darts**, for a lake-free
cell pocket face set. -/
theorem isBoundaryDart_absorbed_iff_of_lakeFree {K : CellPocketFaceSet D eps X i j}
    (hK : CellPocketLakeFree K) (d : X.toCombMap.Dart) :
    Surgery.MapCollapse.IsBoundaryDart X.toCombMap
        (ExteriorComponent.absorbed X.toCombMap K.faces X.outerFace) d ↔
      Surgery.MapCollapse.IsBoundaryDart X.toCombMap K.faces d := by
  rw [absorbed_eq_of_lakeFree hK]

/-- **Removing faces touching the exterior piece keeps a face set lake free.**  Let `K'` be a cell
pocket face set with `K'.faces ⊆ K.faces`, where every removed face has a dart whose reversal
faces the exterior piece of `K`.  If `K` is lake free, so is `K'`. -/
theorem lakeFree_of_boundary_subset {D' : RelGenSet G Lambda} {eps' : ℕ}
    {i' j' : Fin X.rCellCount} {K : CellPocketFaceSet D eps X i j}
    {K' : CellPocketFaceSet D' eps' X i' j'} (hK : CellPocketLakeFree K)
    (hsub : K'.faces ⊆ K.faces)
    (htouch : ∀ f ∈ K.faces, f ∉ K'.faces → ∃ d, X.toCombMap.faceOf d = f ∧
      X.toCombMap.faceOf (X.toCombMap.alpha d) ∈
        ExteriorComponent.component X.toCombMap K.faces X.outerFace) :
    CellPocketLakeFree K' := by
  intro f hf
  by_cases hin : f ∈ K.faces
  · obtain ⟨d, rfl, hα⟩ := htouch _ hin hf
    exact mem_component_of_touch hsub K.outerFace_not_mem hf hα
  · exact component_subset_of_subset hsub K.outerFace_not_mem (hK f hin)

/-- **Removing faces on the boundary cycle keeps a face set lake free.**  The touching hypothesis
of `lakeFree_of_boundary_subset` holds when every removed face carries a dart of the boundary
cycle of `K`. -/
theorem lakeFree_of_boundary_cycle {D' : RelGenSet G Lambda} {eps' : ℕ}
    {i' j' : Fin X.rCellCount} {K : CellPocketFaceSet D eps X i j}
    {K' : CellPocketFaceSet D' eps' X i' j'} (hK : CellPocketLakeFree K)
    (hsub : K'.faces ⊆ K.faces)
    (htouch : ∀ f ∈ K.faces, f ∉ K'.faces → ∃ d ∈ K.boundary.cycle, X.toCombMap.faceOf d = f) :
    CellPocketLakeFree K' := by
  refine lakeFree_of_boundary_subset hK hsub fun f hf hf' => ?_
  obtain ⟨d, hd, hfd⟩ := htouch f hf hf'
  obtain ⟨-, hout⟩ := (K.boundary.cycle_mem_iff d).mp hd
  exact ⟨d, hfd, hK _ hout⟩

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.CellPocketLakeFree
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.cell_mem_component_of_lakeFree
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.mem_component_iff_of_lakeFree
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.absorbed_eq_of_lakeFree
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.isBoundaryDart_absorbed_iff_of_lakeFree
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.lakeFree_of_boundary_subset
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.lakeFree_of_boundary_cycle
