import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseJunctionRefute.Boundary
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketFullArcLakeModel
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPinchedTwoGonModel
import GroupApproximation.Meta.AxiomGuard

/-!
# The disc diagram of the 24-dart counterexample

Lane gl-p10-51.  The map `roseJunctionRefute_M` becomes a disc diagram over `Perm (Fin 3)`.

* The exterior is the face `[15,23,13,11,21,9]`.
* The relator cells are `S = [19,7,5,17,3,14,1]`, reading `1 1 1 1 1 c a⁻¹`, and `K₀ = [0]`,
  reading `a`.  Here `a` is a transposition and `c` a 3-cycle.
* The other four faces are G-faces reading `1`.

Proof route: the boundary reads `c`.  Both relator values are odd, and `c` is even and not `1`.
So the diagram has least area (`roseJunctionRefute_leastArea`), by the sign argument of the base
model (`OsinPocketFullArcLakeModel.sign_of_isRelatorProduct`).

Manuscript status: counterexample/infrastructure for thm:hull.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf

open Equiv GroupApproximation.HullSC
open OsinPocketPinchedTwoGonModel (D)
open OsinPocketFullArcLakeModel (ga gc sign_ga sign_gc sign_of_isRelatorProduct)

abbrev roseJunctionRefute_G := Perm (Fin 3)

/-- The darts `0` and `14` read `a` and `c`, their reverses `1` and `15` read `a⁻¹` and `c⁻¹`,
and all other darts read `1`. -/
def roseJunctionRefute_label (d : Fin 24) : RelLetter roseJunctionRefute_G Empty :=
  .base ((![ga, ga⁻¹, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, gc, gc⁻¹, 1, 1, 1, 1, 1, 1, 1, 1] :
    Fin 24 → roseJunctionRefute_G) d)

def roseJunctionRefute_W : Set (List (RelLetter roseJunctionRefute_G Empty)) :=
  {[.base 1, .base 1, .base 1, .base 1, .base 1, .base gc, .base ga⁻¹], [.base ga]}

def roseJunctionRefute_cellS :
    RelatorCell roseJunctionRefute_M (roseJunctionRefute_face 5) roseJunctionRefute_W where
  face := roseJunctionRefute_face 1
  face_ne_outer := (roseJunctionRefute_face_eq_iff 1 5).not.mpr (by decide)
  word := [.base 1, .base 1, .base 1, .base 1, .base 1, .base gc, .base ga⁻¹]
  word_mem := Or.inl rfl
  conjugator := 1
  reversed := false

def roseJunctionRefute_cellK0 :
    RelatorCell roseJunctionRefute_M (roseJunctionRefute_face 5) roseJunctionRefute_W where
  face := roseJunctionRefute_face 0
  face_ne_outer := (roseJunctionRefute_face_eq_iff 0 5).not.mpr (by decide)
  word := [.base ga]
  word_mem := Or.inr rfl
  conjugator := 1
  reversed := false

/-- **The map as a disc diagram**, with the relator cells `S` and `K₀`. -/
noncomputable def roseJunctionRefute_X : DiscDiagram roseJunctionRefute_W where
  toCombMap := roseJunctionRefute_M
  planar := roseJunctionRefute_planar
  label := roseJunctionRefute_label
  label_alpha := by
    intro d
    fin_cases d <;> exact congrArg RelLetter.base (by decide)
  outerFace := roseJunctionRefute_face 5
  faceBoundary := roseJunctionRefute_boundary
  relatorCells := [roseJunctionRefute_cellS, roseJunctionRefute_cellK0]
  relatorCell_faces_nodup := by
    change [roseJunctionRefute_face 1, roseJunctionRefute_face 0].Nodup
    refine List.nodup_cons.mpr ⟨?_, List.nodup_singleton _⟩
    rw [List.mem_singleton]
    exact (roseJunctionRefute_face_eq_iff 1 0).not.mpr (by decide)
  relatorCell_word := by
    intro C hC
    rcases List.mem_cons.mp hC with rfl | hC
    · change [RelLetter.base (1 : roseJunctionRefute_G), RelLetter.base 1, RelLetter.base 1,
        RelLetter.base 1, RelLetter.base 1, RelLetter.base gc, RelLetter.base ga⁻¹] =
          (roseJunctionRefute_boundary (roseJunctionRefute_face 1)).darts.map
            roseJunctionRefute_label
      rw [roseJunctionRefute_bd_face]
      rfl
    · obtain rfl := List.mem_singleton.mp hC
      change [RelLetter.base ga] =
        (roseJunctionRefute_boundary (roseJunctionRefute_face 0)).darts.map
          roseJunctionRefute_label
      rw [roseJunctionRefute_bd_face]
      rfl
  inner_face := by
    intro f hf
    obtain ⟨i, rfl⟩ : ∃ i, roseJunctionRefute_face i = f :=
      ⟨roseJunctionRefute_faceEquiv f, roseJunctionRefute_faceEquiv.left_inv f⟩
    fin_cases i
    · exact Or.inl ⟨roseJunctionRefute_cellK0, by simp, rfl⟩
    · exact Or.inl ⟨roseJunctionRefute_cellS, by simp, rfl⟩
    · right
      rw [roseJunctionRefute_bd_face]
      decide
    · right
      rw [roseJunctionRefute_bd_face]
      decide
    · right
      rw [roseJunctionRefute_bd_face]
      decide
    · exact (hf rfl).elim
    · right
      rw [roseJunctionRefute_bd_face]
      decide
  boundary_product := by
    rw [roseJunctionRefute_bd_face]
    decide

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.roseJunctionRefute_G
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.roseJunctionRefute_label
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.roseJunctionRefute_W
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.roseJunctionRefute_cellS
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.roseJunctionRefute_cellK0
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.roseJunctionRefute_X
