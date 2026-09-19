import GroupApproximation.GGT.VanKampen.FaceBoundaryRotation
import GroupApproximation.GGT.VanKampen.GFaceEdgeInsertion
import GroupApproximation.GGT.VanKampen.Estimating.GeometricCandidateTransport
import GroupApproximation.GGT.VanKampen.FaceShellingValue

/-!
# Starting an actual G-face traversal at a prescribed corner

Only the chosen G-face's initial dart changes. Its rotated word is still
null in the base group. The planar map, labels, literal exterior word and
complete ordered relator data are unchanged. The identity embedding retains
every selected contiguity avoiding that face, including its shelling.
-/

namespace GroupApproximation.GGT.VanKampen.GFaceRebase

open HullSC Embedded
open scoped Classical
universe u w v
variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}

noncomputable def boundary (Delta : DiscDiagram.{u, w, v} W)
    (f : Delta.toCombMap.Face) (n : ℕ) (g : Delta.toCombMap.Face) :
    FaceBoundary Delta.toCombMap g :=
  if g = f then (Delta.faceBoundary g).rotate n else Delta.faceBoundary g

variable (Delta : DiscDiagram.{u, w, v} W) (f : Delta.toCombMap.Face) (n : ℕ)
  (hf : f ≠ Delta.outerFace) (hcells : ∀ C ∈ Delta.relatorCells, C.face ≠ f)

noncomputable def diagram : DiscDiagram.{u, w, v} W where
  toCombMap := Delta.toCombMap
  planar := Delta.planar
  label := Delta.label
  label_alpha := Delta.label_alpha
  outerFace := Delta.outerFace
  faceBoundary := boundary Delta f n
  relatorCells := Delta.relatorCells
  relatorCell_faces_nodup := Delta.relatorCell_faces_nodup
  relatorCell_word := by
    intro C hC
    simpa only [boundary, if_neg (hcells C hC)] using Delta.relatorCell_word C hC
  inner_face := by
    intro g hgo
    by_cases hg : g = f
    · subst g
      right
      simp only [boundary, FaceBoundary.rotate]
      change RelLetter.listVal (dartWord Delta ((Delta.faceBoundary f).darts.rotate n)) = 1
      rw [listVal_dartWord_rotate]
      have hnull := GFaceEdgeInsertion.gFace_value Delta f hf hcells
      change RelLetter.listVal (dartWord Delta (Delta.faceBoundary f).darts) = 1 at hnull
      rw [hnull]
      group
    · simpa only [boundary, if_neg hg] using Delta.inner_face g hgo
  boundary_product := by
    simpa only [boundary, if_neg hf.symm] using Delta.boundary_product

theorem boundaryWord_eq : (diagram Delta f n hf hcells).boundaryWord = Delta.boundaryWord := by
  change RelWord.revInv ((boundary Delta f n Delta.outerFace).darts.map Delta.label) = _
  simp only [boundary, if_neg hf.symm]
  rfl

def cells : Surgery.OrderedRCellMap Delta (diagram Delta f n hf hcells) id where
  cell := id
  face_eq _ := rfl
  word_eq _ := rfl
  conjugator_eq _ := rfl
  reversed_eq _ := rfl
  list_eq := (List.map_id _).symm

noncomputable def replacement : Surgery.OrderedGRegionReplacement.{u, w, v, v} Delta :=
  ⟨diagram Delta f n hf hcells, boundaryWord_eq Delta f n hf hcells,
    (cells Delta f n hf hcells).orderedTransport⟩

def embedding : DiscEmbeddingAway Delta (diagram Delta f n hf hcells) f where
  darts := Function.Embedding.refl _
  faces := Function.Embedding.refl _
  alpha _ := rfl
  label _ := rfl
  outer := rfl
  face_boundary g hg := by
    change (boundary Delta f n g).darts = (Delta.faceBoundary g).darts.map id
    rw [boundary, if_neg hg, List.map_id]
  facePerm _ _ := rfl

theorem label_admissible (D : RelGenSet G Lambda)
    (hlabel : ∀ d, D.IsLetter (Delta.label d)) :
    ∀ d, D.IsLetter ((diagram Delta f n hf hcells).label d) := hlabel

theorem initial_dart (k : Fin (Delta.faceBoundary f).darts.length) :
    ((diagram Delta f k.val hf hcells).faceBoundary f).darts.head
      ((diagram Delta f k.val hf hcells).faceBoundary f).nonempty =
        (Delta.faceBoundary f).darts.get k := by
  change (boundary Delta f k.val f).darts.head (boundary Delta f k.val f).nonempty = _
  simp only [boundary]
  exact (Delta.faceBoundary f).rotate_head k

def cornerIndex (start finish : Fin (Delta.faceBoundary f).darts.length) :
    Fin ((diagram Delta f start.val hf hcells).faceBoundary f).darts.length :=
  ⟨(Delta.faceBoundary f).forwardOffset start finish, by
    change _ < (boundary Delta f start.val f).darts.length
    simpa only [boundary, ite_true, FaceBoundary.rotate, List.length_rotate] using
      (Delta.faceBoundary f).forwardOffset_lt start finish⟩

theorem terminal_dart (start finish : Fin (Delta.faceBoundary f).darts.length) :
    ((diagram Delta f start.val hf hcells).faceBoundary f).darts.get
      (cornerIndex Delta f hf hcells start finish) = (Delta.faceBoundary f).darts.get finish := by
  simp only [diagram, boundary, ite_true, cornerIndex, FaceBoundary.rotate,
    List.get_eq_getElem, List.getElem_rotate, FaceBoundary.forwardOffset_add_mod]

/-- The actual identity embedding preserves all full candidate data away
from the rebased G-face, and therefore preserves the family's exact weight. -/
theorem exists_retained_family (D : RelGenSet G Lambda) (eps : ℕ)
    (family : Finset (GeometricCandidate D eps Delta))
    (havoid : ∀ a ∈ family, f ∉ a.1)
    (hpairwise : EstimatingSelection.PairwiseCompatible GeometricCandidate.Compatible family) :
    ∃ family' : Finset (GeometricCandidate D eps (diagram Delta f n hf hcells)),
      EstimatingSelection.PairwiseCompatible GeometricCandidate.Compatible family' ∧
      family'.card = family.card ∧
      EstimatingSelection.familyWeight GeometricCandidate.weight family' =
        EstimatingSelection.familyWeight GeometricCandidate.weight family := by
  let E := embedding Delta f n hf hcells
  let C := cells Delta f n hf hcells
  exact ⟨E.geometricFamily C hcells hf family havoid,
    E.geometricFamily_pairwise C hcells hf family havoid hpairwise,
    E.geometricFamily_card C hcells hf family havoid,
    E.geometricFamily_weight C hcells hf family havoid⟩

end GroupApproximation.GGT.VanKampen.GFaceRebase

#audit_axioms GroupApproximation.GGT.VanKampen.GFaceRebase.diagram
#audit_axioms GroupApproximation.GGT.VanKampen.GFaceRebase.replacement
#audit_axioms GroupApproximation.GGT.VanKampen.GFaceRebase.embedding
#audit_axioms GroupApproximation.GGT.VanKampen.GFaceRebase.initial_dart
#audit_axioms GroupApproximation.GGT.VanKampen.GFaceRebase.terminal_dart
#audit_axioms GroupApproximation.GGT.VanKampen.GFaceRebase.exists_retained_family
