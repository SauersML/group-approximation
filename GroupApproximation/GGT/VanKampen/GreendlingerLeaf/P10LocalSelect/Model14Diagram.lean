import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LocalSelect.Model14Map
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketFullArcLakeModel
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPinchedTwoGonModel
import GroupApproximation.Meta.AxiomGuard

/-!
# The 14-dart shared-rose model: the disc diagram

The map `m14_M` becomes a disc diagram over `Perm (Fin 3)`.

* The exterior is the face `E = [3,12,5]`.
* The relator cells are `K = [0,2]`, reading `a 1`, and `S = [1,7,10]`, reading `a⁻¹ c 1`, where
  `a` is a transposition and `c` a 3-cycle.
* The other faces, `P_B = [4,8,6]` reading `c 1 c⁻¹`, the lake `[9]` and the pads `[11]`, `[13]`,
  are G-faces reading `1`.

Proof route: the boundary reads `c`.  Both relator values are odd, and `c` is even and not `1`,
so the diagram has least area (`m14_leastArea`), by the sign argument of
`OsinPocketFullArcLakeModel.sign_of_isRelatorProduct`.  Same pattern as
`P10RoseJunctionRefute/Diagram` and `P10RoseJunctionRefute/Area`.

Manuscript status: infrastructure (a truth witness) for thm:hull.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LocalSelect

open Equiv GroupApproximation.HullSC
open OsinPocketPinchedTwoGonModel (D)
open OsinPocketFullArcLakeModel (ga gc sign_ga sign_gc sign_of_isRelatorProduct)

abbrev m14_G := Perm (Fin 3)

/-- The dart `a_S = 0` reads `a`, the darts `b_E = 4` and `α b_S = 7` read `c`, their reverses the
inverses, and every other dart reads `1`. -/
def m14_label (d : Fin 14) : RelLetter m14_G Empty :=
  .base ((![ga, ga⁻¹, 1, 1, gc, gc⁻¹, gc⁻¹, gc, 1, 1, 1, 1, 1, 1] : Fin 14 → m14_G) d)

def m14_W : Set (List (RelLetter m14_G Empty)) :=
  {[.base ga, .base 1], [.base ga⁻¹, .base gc, .base 1]}

def m14_cellK : RelatorCell m14_M (m14_face 5) m14_W where
  face := m14_face 0
  face_ne_outer := (m14_face_eq_iff 0 5).not.mpr (by decide)
  word := [.base ga, .base 1]
  word_mem := Or.inl rfl
  conjugator := 1
  reversed := false

def m14_cellS : RelatorCell m14_M (m14_face 5) m14_W where
  face := m14_face 3
  face_ne_outer := (m14_face_eq_iff 3 5).not.mpr (by decide)
  word := [.base ga⁻¹, .base gc, .base 1]
  word_mem := Or.inr rfl
  conjugator := 1
  reversed := false

/-- **The map as a disc diagram**, with the relator cells `K` and `S`. -/
noncomputable def m14_X : DiscDiagram m14_W where
  toCombMap := m14_M
  planar := m14_planar
  label := m14_label
  label_alpha := by
    intro d
    fin_cases d <;> exact congrArg RelLetter.base (by decide)
  outerFace := m14_face 5
  faceBoundary := m14_boundary
  relatorCells := [m14_cellK, m14_cellS]
  relatorCell_faces_nodup := by
    change [m14_face 0, m14_face 3].Nodup
    refine List.nodup_cons.mpr ⟨?_, List.nodup_singleton _⟩
    rw [List.mem_singleton]
    exact (m14_face_eq_iff 0 3).not.mpr (by decide)
  relatorCell_word := by
    intro C hC
    rcases List.mem_cons.mp hC with rfl | hC
    · change [RelLetter.base ga, RelLetter.base (1 : m14_G)] =
        (m14_boundary (m14_face 0)).darts.map m14_label
      rw [m14_bd_face]
      rfl
    · obtain rfl := List.mem_singleton.mp hC
      change [RelLetter.base ga⁻¹, RelLetter.base gc, RelLetter.base (1 : m14_G)] =
        (m14_boundary (m14_face 3)).darts.map m14_label
      rw [m14_bd_face]
      rfl
  inner_face := by
    intro f hf
    obtain ⟨i, rfl⟩ : ∃ i, m14_face i = f := ⟨m14_faceEquiv f, m14_faceEquiv.left_inv f⟩
    fin_cases i
    · exact Or.inl ⟨m14_cellK, by simp, rfl⟩
    · right
      rw [m14_bd_face]
      decide
    · right
      rw [m14_bd_face]
      decide
    · exact Or.inl ⟨m14_cellS, by simp, rfl⟩
    · right
      rw [m14_bd_face]
      decide
    · exact (hf rfl).elim
    · right
      rw [m14_bd_face]
      decide
  boundary_product := by
    rw [m14_bd_face]
    decide

instance m14_instNeZero : NeZero m14_X.rCellCount := ⟨by decide⟩
instance m14_instOfNatX (n : ℕ) : OfNat m14_X.toCombMap.Dart n := inferInstanceAs (OfNat (Fin 14) n)
instance m14_instDecEqX : DecidableEq m14_X.toCombMap.Dart := inferInstanceAs (DecidableEq (Fin 14))

/-- The kept cell `K`. -/
def m14_iK : Fin m14_X.rCellCount := ⟨0, by decide⟩

/-- The source cell `S`. -/
def m14_iS : Fin m14_X.rCellCount := ⟨1, by decide⟩

theorem m14_letters : ∀ d, (symmetricLabelAlphabet D).IsLetter (m14_X.label d) := fun _ =>
  Or.inl (Set.mem_univ _)

theorem m14_relSigns : ∀ r ∈ RelLetter.listVal '' m14_W, Perm.sign r = -1 := by
  rintro r ⟨word, hword, rfl⟩
  simp only [m14_W, Set.mem_insert_iff, Set.mem_singleton_iff] at hword
  rcases hword with rfl | rfl
  · rw [show RelLetter.listVal ([.base ga, .base 1] : List (RelLetter m14_G Empty)) = ga
      by decide]
    exact sign_ga
  · rw [show RelLetter.listVal ([.base ga⁻¹, .base gc, .base 1] :
        List (RelLetter m14_G Empty)) = ga⁻¹ * gc by decide,
      Perm.sign_mul, Perm.sign_inv, sign_ga, sign_gc, mul_one]

theorem m14_bdValue : m14_X.boundaryValue = gc := by
  change RelLetter.listVal (RelWord.revInv
    ((m14_boundary (m14_face 5)).darts.map m14_label)) = gc
  rw [m14_bd_face]
  decide

/-- **The diagram has least area.** -/
theorem m14_leastArea : m14_X.LeastArea := by
  intro m hm
  rw [m14_bdValue] at hm
  have hsign := sign_of_isRelatorProduct m14_relSigns hm
  rw [sign_gc] at hsign
  change 2 ≤ m
  rcases m with _ | _ | m
  · exact absurd hm.eq_one_of_index_zero (by decide)
  · exact absurd hsign (by decide)
  · omega

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LocalSelect

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LocalSelect.m14_X
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LocalSelect.m14_letters
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LocalSelect.m14_leastArea
