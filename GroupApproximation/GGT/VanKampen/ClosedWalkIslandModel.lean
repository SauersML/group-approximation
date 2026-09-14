import GroupApproximation.GGT.VanKampen.CactusBoundary
import GroupApproximation.GGT.VanKampen.FaceShelling
import GroupApproximation.GGT.VanKampen.ClosedWalkEnclosedSubdiagram
import GroupApproximation.GGT.VanKampen.ClosedWalkPinchSplit
import GroupApproximation.Meta.AxiomGuard

/-!
# The smallest island: a closed walk along a bridge

A model test for `ClosedWalkEnclosedSubdiagram`, in the island case of Case 1 of Osin's Lemma 9.4
(arXiv:math/0411039v3, §9): the side along the polygon face runs through a cutting path `t`
around an island and back along `t⁻¹`.

The map has six darts and two vertices `a = {0,1,2}` and `b = {3,4,5}`.  A loop `0/1` at `a` bounds
the relator face `Π = [0]`, a loop `4/5` at `b` bounds the relator face `I = [4]`, and the bridge
`t = 2/3` joins `a` to `b`.  The exterior face `f = [1,2,5,3]` lies on both sides of `t` and
traverses it twice.

* `planar`: the map is planar (`V − E + F = 2 − 3 + 3`).
* `diagram`: a disc diagram over `Perm (Fin 3)` with relator cells on `Π` and `I`.
* `pocketWalk_isClosedDartWalk`, `pocketWalk_not_isSimpleClosedWalk`: the pocket walk
  `[2,4,3,0]`, the inverse of the exterior walk, is a closed dart walk and is not simple, since it
  uses both darts of `t`.  A pocket region reads a simple walk
  (`PocketRegion.isSimpleClosedWalk_invDarts_outer`), so the pocket route does not apply here.
* `islandFaces_no_common_edge`: no edge has both faces in `{Π, I}`; the enclosed faces are joined
  only along `t`.
* `enclosedFaceSet`: `{Π, I}` is enclosed by the exterior walk `[1,2,5,3]` in the sense of
  `EnclosedFaceSet`, bridge darts and turning condition included.
* `enclosedSubdiagram_realized`: calibration.  The clauses of
  `ClosedWalkEnclosedSubdiagramStatement` hold at this face set, realized by the diagram itself,
  whose boundary traverses `t` twice.

## Manuscript status

Model test for infrastructure of `thm:hull` (tex 1636, through Osin's Lemmas 9.4 and 9.7);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.ClosedWalkIslandModel

open Equiv GroupApproximation.HullSC GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides

def alpha : Perm (Fin 6) where
  toFun := ![1, 0, 3, 2, 5, 4]
  invFun := ![1, 0, 3, 2, 5, 4]
  left_inv := by decide
  right_inv := by decide

def facePerm : Perm (Fin 6) where
  toFun := ![0, 2, 5, 1, 4, 3]
  invFun := ![0, 3, 1, 5, 4, 2]
  left_inv := by decide
  right_inv := by decide

def M : CombMap where
  Dart := Fin 6
  dartFintype := inferInstance
  alpha := alpha
  sigma := facePerm * alpha
  alpha_involutive := by intro d; fin_cases d <;> rfl
  alpha_fixedPointFree := by decide

instance : DecidableEq M.Dart := inferInstanceAs (DecidableEq (Fin 6))
instance (n : ℕ) : OfNat M.Dart n := inferInstanceAs (OfNat (Fin 6) n)

def faceClass : Fin 6 → Fin 3 := ![0, 2, 2, 2, 1, 2]
def faceRep : Fin 3 → Fin 6 := ![0, 4, 1]

noncomputable def faceEquiv : M.Face ≃ Fin 3 :=
  OrbitClassifier.orbitEquiv M.facePerm faceClass faceRep
    (by decide) (by decide) (by decide)

def face (i : Fin 3) : M.Face := M.faceOf (faceRep i)

@[simp] theorem faceEquiv_face (i : Fin 3) : faceEquiv (face i) = i := by
  change faceClass (faceRep i) = i
  fin_cases i <;> rfl

theorem faceOf_eq_face (d : Fin 6) (i : Fin 3) :
    M.faceOf d = face i ↔ faceClass d = i := by
  rw [← faceEquiv.injective.eq_iff, faceEquiv_face]
  rfl

theorem face_eq_iff (i j : Fin 3) : face i = face j ↔ i = j := by
  rw [← faceEquiv.injective.eq_iff, faceEquiv_face, faceEquiv_face]

def vertexClass : Fin 6 → Fin 2 := ![0, 0, 0, 1, 1, 1]

noncomputable def vertexEquiv : M.Vertex ≃ Fin 2 :=
  OrbitClassifier.orbitEquiv M.sigma vertexClass (![0, 3] : Fin 2 → Fin 6)
    (by decide) (by decide) (by decide)

theorem vertexOf_eq_iff (d e : Fin 6) :
    M.vertexOf d = M.vertexOf e ↔ vertexClass d = vertexClass e := by
  rw [← vertexEquiv.injective.eq_iff]
  rfl

theorem planar : M.IsPlanar := by
  constructor
  · have hstep : ∀ d : Fin 6, Relation.EqvGen M.Adjacent 0 d := by
      have trans {d e f : M.Dart}
          (hde : Relation.EqvGen M.Adjacent d e)
          (hef : Relation.EqvGen M.Adjacent e f) :
          Relation.EqvGen M.Adjacent d f := .trans _ _ _ hde hef
      have h01 : Relation.EqvGen M.Adjacent 0 1 := .rel _ _ (Or.inl rfl)
      have h02 : Relation.EqvGen M.Adjacent 0 2 := .rel _ _ (Or.inr rfl)
      have h23 : Relation.EqvGen M.Adjacent 2 3 := .rel _ _ (Or.inl rfl)
      have h35 : Relation.EqvGen M.Adjacent 3 5 := .rel _ _ (Or.inr rfl)
      have h54 : Relation.EqvGen M.Adjacent 5 4 := .rel _ _ (Or.inl rfl)
      intro d
      fin_cases d
      · exact .refl _
      · exact h01
      · exact h02
      · exact trans h02 h23
      · exact trans (trans (trans h02 h23) h35) h54
      · exact trans (trans h02 h23) h35
    intro d e
    exact .trans _ _ _ (.symm _ _ (hstep d)) (hstep e)
  · have hv : M.vertexCount = 2 := (Nat.card_congr vertexEquiv).trans (by simp)
    have hf : M.faceCount = 3 := (Nat.card_congr faceEquiv).trans (by simp)
    have hd : M.dartCount = 6 := by simp [CombMap.dartCount, M]
    have he := M.dartCount_eq_two_mul_edgeCount
    unfold CombMap.eulerCharacteristic
    rw [hv, hf]
    have heq : M.edgeCount = 3 := by omega
    rw [heq]
    norm_num

def faceDarts : Fin 3 → List (Fin 6) := ![[0], [4], [1, 2, 5, 3]]

noncomputable def indexedBoundary (i : Fin 3) : FaceBoundary M (face i) where
  darts := faceDarts i
  nonempty := by change faceDarts i ≠ ([] : List (Fin 6)); fin_cases i <;> decide
  nodup := by fin_cases i <;> decide
  mem_iff := by
    intro d
    rw [faceOf_eq_face]
    fin_cases i <;> fin_cases d <;> decide
  chain := by fin_cases i <;> decide
  closes := by fin_cases i <;> decide
  length_eq_degree := by
    have h := closedOrbitList.length_eq_orbitDegree M.facePerm (faceRep i)
    have hd : closedOrbitList M.facePerm (faceRep i) = faceDarts i := by
      fin_cases i <;> decide
    rw [hd] at h
    exact h

noncomputable def boundary (f : M.Face) : FaceBoundary M f :=
  (faceEquiv.left_inv f) ▸ indexedBoundary (faceEquiv f)

@[simp] theorem boundary_face_darts (i : Fin 3) :
    (boundary (face i)).darts = faceDarts i := by
  have htransport {f g : M.Face} (h : f = g) (B : FaceBoundary M f) :
      (h ▸ B).darts = B.darts := by cases h; rfl
  unfold boundary
  rw [htransport]
  exact congrArg faceDarts (faceEquiv_face i)

abbrev G := Perm (Fin 3)

def ga : G := Equiv.swap 0 1
def gb : G := Equiv.swap 1 2
def gt : G := Equiv.swap 0 2

/-- The loop of `Π` reads `a`, the loop of `I` reads `b`, and the bridge reads `t`. -/
def label (d : Fin 6) : RelLetter G Empty :=
  .base ((![ga, ga⁻¹, gt, gt⁻¹, gb, gb⁻¹] : Fin 6 → G) d)

def W : Set (List (RelLetter G Empty)) := {[.base ga], [.base gb]}

def cellP : RelatorCell M (face 2) W where
  face := face 0
  face_ne_outer := (face_eq_iff 0 2).not.mpr (by decide)
  word := [.base ga]
  word_mem := Or.inl rfl
  conjugator := 1
  reversed := false

def cellI : RelatorCell M (face 2) W where
  face := face 1
  face_ne_outer := (face_eq_iff 1 2).not.mpr (by decide)
  word := [.base gb]
  word_mem := Or.inr rfl
  conjugator := gt
  reversed := false

noncomputable def diagram : DiscDiagram W where
  toCombMap := M
  planar := planar
  label := label
  label_alpha := by
    intro d
    fin_cases d <;> exact congrArg RelLetter.base (by decide)
  outerFace := face 2
  faceBoundary := boundary
  relatorCells := [cellI, cellP]
  relatorCell_faces_nodup := by
    change [face 1, face 0].Nodup
    refine List.nodup_cons.mpr ⟨?_, List.nodup_singleton _⟩
    rw [List.mem_singleton]
    exact (face_eq_iff 1 0).not.mpr (by decide)
  relatorCell_word := by
    intro C hC
    rcases List.mem_cons.mp hC with rfl | hC
    · change [RelLetter.base gb] = (boundary (face 1)).darts.map label
      rw [boundary_face_darts]
      rfl
    · obtain rfl := List.mem_singleton.mp hC
      change [RelLetter.base ga] = (boundary (face 0)).darts.map label
      rw [boundary_face_darts]
      rfl
  inner_face := by
    intro f hf
    obtain ⟨i, rfl⟩ : ∃ i, face i = f := ⟨faceEquiv f, faceEquiv.left_inv f⟩
    fin_cases i
    · exact Or.inl ⟨cellP, by simp, rfl⟩
    · exact Or.inl ⟨cellI, by simp, rfl⟩
    · exact (hf rfl).elim
  boundary_product := by
    rw [boundary_face_darts]
    decide

instance (n : ℕ) : OfNat diagram.toCombMap.Dart n := inferInstanceAs (OfNat (Fin 6) n)
instance : DecidableEq diagram.toCombMap.Dart := inferInstanceAs (DecidableEq (Fin 6))

/-- The exterior walk: the darts of `f`, the bridge twice. -/
def outerWalk : List M.Dart := [1, 2, 5, 3]

/-- The pocket walk `[2,4,3,0]` is a closed dart walk. -/
theorem pocketWalk_isClosedDartWalk : IsClosedDartWalk M ([2, 4, 3, 0] : List M.Dart) := by
  refine ⟨by decide, ?_, ?_⟩
  · simp only [vertexOf_eq_iff]
    decide
  · rw [vertexOf_eq_iff]
    decide

/-- The pocket walk uses both darts of the bridge, so it is not a simple closed walk. -/
theorem pocketWalk_not_isSimpleClosedWalk :
    ¬ IsSimpleClosedWalk M ([2, 4, 3, 0] : List M.Dart) :=
  fun h => h.alpha_not_mem 2 (by decide) (by decide)

/-- The pocket walk is the inverse of the exterior walk. -/
theorem invDarts_outerWalk : Embedded.invDarts diagram outerWalk = [2, 4, 3, 0] := by
  decide

/-- The enclosed faces `Π` and `I`. -/
def islandFaces : Finset M.Face :=
  Finset.cons (face 0) {face 1} fun h =>
    absurd ((face_eq_iff 0 1).mp (Finset.mem_singleton.mp h)) (by decide)

theorem mem_islandFaces (d : Fin 6) :
    M.faceOf d ∈ islandFaces ↔ faceClass d = 0 ∨ faceClass d = 1 := by
  simp only [islandFaces, Finset.mem_cons, Finset.mem_singleton, faceOf_eq_face]

/-- No edge has both faces in `{Π, I}`: the enclosed faces meet only along the bridge. -/
theorem islandFaces_no_common_edge (d : M.Dart) :
    M.faceOf d ∈ islandFaces → M.faceOf (M.alpha d) ∉ islandFaces := by
  rw [mem_islandFaces, mem_islandFaces]
  fin_cases d <;> decide

theorem walkKeep_all (x : M.Dart) : walkKeep M outerWalk x := by
  unfold walkKeep
  fin_cases x <;> decide

/-- At every dart of the exterior walk, one rotation from its reverse is again a walk dart. -/
theorem sigma_alpha_mem (d : M.Dart) : d ∈ outerWalk → M.sigma (M.alpha d) ∈ outerWalk := by
  fin_cases d <;> decide

/-- **`{Π, I}` is enclosed by the exterior walk.** -/
theorem enclosedFaceSet : EnclosedFaceSet diagram islandFaces outerWalk where
  outerFace_not_mem := by
    change M.faceOf (1 : M.Dart) ∉ islandFaces
    rw [mem_islandFaces]
    decide
  ne_nil := List.cons_ne_nil _ _
  nodup := by decide
  chain := by
    change List.IsChain (fun d e => M.vertexOf (M.alpha d) = M.vertexOf e) outerWalk
    simp only [vertexOf_eq_iff]
    decide
  closes := (vertexOf_eq_iff (M.alpha 3) 1).mpr (by decide)
  mem_iff := by
    intro d
    change d ∈ outerWalk ↔ M.faceOf d ∉ islandFaces ∧
      (M.faceOf (M.alpha d) ∈ islandFaces ∨ M.alpha d ∈ outerWalk)
    simp only [mem_islandFaces]
    fin_cases d <;> decide
  turn_mem := by
    intro d hd m hm hkeep hmin
    rcases Nat.lt_or_ge 1 m with h1 | h1
    · exact absurd (walkKeep_all _) (hmin 1 Nat.one_pos h1)
    · obtain rfl : m = 1 := by omega
      rw [pow_one]
      exact sigma_alpha_mem d hd

open scoped Classical in
/-- **Calibration.**  The clauses of `ClosedWalkEnclosedSubdiagramStatement` hold at `{Π, I}`,
realized by the diagram itself, whose boundary traverses the bridge twice. -/
theorem enclosedSubdiagram_realized :
    ∃ Xi : DiscDiagram.{0, 0, 0} W,
      Xi.boundaryWord = Embedded.dartWord diagram (Embedded.invDarts diagram outerWalk) ∧
      Xi.rCellCount ≤ (diagram.relatorCells.filter fun C => C.face ∈ islandFaces).length ∧
      ((∃ C ∈ diagram.relatorCells, C.face ∈ islandFaces) → 0 < Xi.rCellCount) ∧
      (∃ ι : Fin Xi.rCellCount ↪ Fin diagram.rCellCount, ∀ j : Fin Xi.rCellCount,
        (Embedded.cell Xi j).word = (Embedded.cell diagram (ι j)).word ∧
          (Embedded.cell diagram (ι j)).face ∈ islandFaces) ∧
      (diagram.LeastArea → Xi.LeastArea) := by
  have hout : Embedded.outerDarts diagram = Embedded.invDarts diagram outerWalk := by
    change ((boundary (face 2)).darts.reverse.map M.alpha) = outerWalk.reverse.map M.alpha
    rw [boundary_face_darts]
    rfl
  have hfaces : ∀ C ∈ diagram.relatorCells, C.face ∈ islandFaces := by
    intro C hC
    rcases List.mem_cons.mp hC with rfl | hC
    · change face 1 ∈ islandFaces
      simp [islandFaces]
    · obtain rfl := List.mem_singleton.mp hC
      change face 0 ∈ islandFaces
      simp [islandFaces]
  refine ⟨diagram, ?_, ?_, fun _ => Nat.zero_lt_two, ⟨Function.Embedding.refl _, ?_⟩, id⟩
  · rw [← hout, Embedded.dartWord_outerDarts]
  · have hfilter :
        (diagram.relatorCells.filter fun C => C.face ∈ islandFaces) = diagram.relatorCells :=
      List.filter_eq_self.mpr fun C hC => decide_eq_true (hfaces C hC)
    exact (congrArg List.length hfilter).ge
  · intro j
    exact ⟨rfl, hfaces _ (Embedded.cell_mem diagram j)⟩

end GroupApproximation.GGT.VanKampen.ClosedWalkIslandModel

open GroupApproximation.GGT.VanKampen.ClosedWalkIslandModel

#audit_axioms planar
#audit_axioms diagram
#audit_axioms pocketWalk_isClosedDartWalk
#audit_axioms pocketWalk_not_isSimpleClosedWalk
#audit_axioms invDarts_outerWalk
#audit_axioms islandFaces_no_common_edge
#audit_axioms enclosedFaceSet
#audit_axioms enclosedSubdiagram_realized
