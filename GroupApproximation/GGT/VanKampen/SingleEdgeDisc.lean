import GroupApproximation.GGT.VanKampen.DiscDiagram
import GroupApproximation.GGT.VanKampen.CombMapReduction
import GroupApproximation.GGT.HullSCRelatorFamily
import GroupApproximation.Meta.AxiomGuard

/-!
# The disc of a single edge

The combinatorial map with two darts, one edge and two vertices of valence one has a
single face, traversed by both darts.  Labelling the edge by a letter `u` gives a disc
diagram over any relator family whose boundary word is the cancelling pair
`u u⁻¹` and which has no relator cells.  It is the base case of the literal van
Kampen construction: every freely trivial nonempty word is obtained from it by
attaching pendant edges.

* `map`, with `planar_map`: the one-edge map is planar.
* `diagram`, with `diagram_boundaryWord`, `diagram_rCellCount` and
  `diagram_cover`: the disc reading `u u⁻¹`.
-/

namespace GroupApproximation.GGT.VanKampen.SingleEdgeDisc

open Equiv

universe u w

/-- Edge reversal on the two darts of one edge. -/
def alphaPerm : Perm Bool := ⟨not, not, Bool.not_not, Bool.not_not⟩

/-- **The map of a single edge.**  Both vertices have valence one. -/
def map : CombMap.{0} where
  Dart := Bool
  dartFintype := inferInstance
  alpha := alphaPerm
  sigma := 1
  alpha_involutive := Bool.not_not
  alpha_fixedPointFree := fun b => by cases b <;> decide

theorem vertexCount_eq : map.vertexCount = 2 := by
  have e : map.Vertex ≃ Bool := by
    refine Equiv.ofBijective (Quotient.lift id fun _ _ h => Equiv.Perm.sameCycle_one.mp h)
      ⟨?_, fun b => ⟨Quotient.mk _ b, rfl⟩⟩
    intro x y hxy
    rcases x with ⟨a⟩
    rcases y with ⟨b⟩
    exact Quot.sound (Equiv.Perm.sameCycle_one.mpr hxy)
  rw [CombMap.vertexCount, Nat.card_congr e, Nat.card_eq_fintype_card]
  exact Fintype.card_bool

theorem edgeCount_eq : map.edgeCount = 1 := by
  have h := map.dartCount_eq_two_mul_edgeCount
  have hd : map.dartCount = 2 := by
    rw [CombMap.dartCount, Nat.card_eq_fintype_card]
    exact Fintype.card_bool
  omega

/-- The two darts lie on one face. -/
theorem faceSubsingleton : Subsingleton map.Face := by
  refine ⟨fun x y => ?_⟩
  rcases x with ⟨a⟩
  rcases y with ⟨b⟩
  apply Quot.sound
  by_cases hab : a = b
  · subst hab
    exact Equiv.Perm.SameCycle.rfl
  · have hb : b = !a := by cases a <;> cases b <;> simp_all
    subst hb
    exact Equiv.Perm.SameCycle.rfl.apply_right

theorem faceCount_eq : map.faceCount = 1 :=
  Nat.card_eq_one_iff_unique.mpr ⟨faceSubsingleton, ⟨map.faceOf true⟩⟩

theorem connected_map : map.IsConnected := by
  intro a b
  by_cases hab : a = b
  · subst hab
    exact Relation.EqvGen.refl _
  · have hb : b = !a := by cases a <;> cases b <;> simp_all
    subst hb
    exact Relation.EqvGen.rel _ _ (Or.inl rfl)

/-- **The one-edge map is planar.** -/
theorem planar_map : map.IsPlanar := by
  refine ⟨connected_map, ?_⟩
  unfold CombMap.eulerCharacteristic
  rw [vertexCount_eq, edgeCount_eq, faceCount_eq]
  norm_num

/-- The single face, traversed by both darts. -/
def faceBoundary (f : map.Face) : FaceBoundary map f where
  darts := [true, false]
  nonempty := List.cons_ne_nil _ _
  nodup := List.nodup_cons.mpr ⟨by simp, List.nodup_singleton _⟩
  mem_iff := fun d => ⟨fun _ => faceSubsingleton.allEq _ _, fun _ => by cases d <;> simp⟩
  chain := List.isChain_cons_cons.mpr ⟨rfl, List.IsChain.singleton _⟩
  closes := rfl
  length_eq_degree := by
    have hall : ∀ d : map.Dart, map.faceOf d = f := fun d => faceSubsingleton.allEq _ _
    change 2 = Nat.card {d : map.Dart // (Quotient.mk'' d : CombMap.Orbit map.facePerm) = f}
    exact ((Nat.card_congr (Equiv.subtypeUnivEquiv hall)).trans
      (Nat.card_eq_fintype_card.trans Fintype.card_bool)).symm

variable {G : Type u} [Group G] {Lambda : Type w}

/-- The edge reads `u` in one direction and its formal inverse in the other. -/
def label (letter : RelLetter G Lambda) : Bool → RelLetter G Lambda
  | true => letter
  | false => HullSC.RelWord.inv letter

theorem label_alpha (letter : RelLetter G Lambda) (d : map.Dart) :
    label letter (map.alpha d) = HullSC.RelWord.inv (label letter d) := by
  cases d
  · exact (HullSC.RelWord.inv_inv_letter letter).symm
  · rfl

variable (W : Set (List (RelLetter G Lambda))) (letter : RelLetter G Lambda)

/-- **The disc reading `u u⁻¹`**, with no relator cells. -/
def diagram : DiscDiagram.{u, w, 0} W where
  toCombMap := map
  planar := planar_map
  label := label letter
  label_alpha := label_alpha letter
  outerFace := map.faceOf true
  faceBoundary := faceBoundary
  relatorCells := []
  relatorCell_faces_nodup := List.nodup_nil
  relatorCell_word := fun C hC => by cases hC
  inner_face := fun f hf => absurd (faceSubsingleton.allEq f _) hf
  boundary_product := by
    show (1 : G) = RelLetter.listVal (HullSC.RelWord.revInv [letter, HullSC.RelWord.inv letter])
    rw [HullSC.RelWord.listVal_revInv, HullSC.RelWord.listVal_cons,
      HullSC.RelWord.listVal_singleton, HullSC.RelWord.val_inv, mul_inv_cancel, inv_one]

theorem diagram_boundaryWord :
    (diagram W letter).boundaryWord = [letter, HullSC.RelWord.inv letter] := by
  show HullSC.RelWord.revInv [letter, HullSC.RelWord.inv letter] =
    [letter, HullSC.RelWord.inv letter]
  simp only [HullSC.RelWord.revInv_cons, HullSC.RelWord.inv_inv_letter]
  rfl

theorem diagram_rCellCount : (diagram W letter).rCellCount = 0 := rfl

/-- The single-edge disc has no inner face, so it is relator-covered. -/
theorem diagram_cover : RelatorCellCover (diagram W letter) :=
  ⟨fun f hf => absurd (faceSubsingleton.allEq f _) hf⟩

end GroupApproximation.GGT.VanKampen.SingleEdgeDisc

#audit_axioms GroupApproximation.GGT.VanKampen.SingleEdgeDisc.planar_map
#audit_axioms GroupApproximation.GGT.VanKampen.SingleEdgeDisc.diagram
#audit_axioms GroupApproximation.GGT.VanKampen.SingleEdgeDisc.diagram_boundaryWord
#audit_axioms GroupApproximation.GGT.VanKampen.SingleEdgeDisc.diagram_cover
