import GroupApproximation.GGT.HullSCRelativeExteriorArcConversionStatement
import GroupApproximation.GGT.VanKampen.CactusBoundary
import GroupApproximation.GGT.VanKampen.FaceShelling
import GroupApproximation.Meta.AxiomGuard

/-!
# A based relator need not start at its exterior arc

The map below has six darts: a bridge and two loops.  Its three face cycles
are `[0,2,1]`, `[3,4]`, and `[5]`.  The middle face is a G-cell digon between
the relator's middle letter and the outer boundary.  The relator is based at
the other end of the bridge.  This distinguishes a cyclic exterior arc from
a prefix of the stored relator word.
-/

namespace GroupApproximation.GGT.VanKampen.ExteriorArcCounterexample

open Equiv GroupApproximation.HullSC GroupApproximation.WordMetric

def alpha : Perm (Fin 6) where
  toFun := ![1, 0, 3, 2, 5, 4]
  invFun := ![1, 0, 3, 2, 5, 4]
  left_inv := by decide
  right_inv := by decide

def facePerm : Perm (Fin 6) where
  toFun := ![2, 0, 1, 4, 3, 5]
  invFun := ![1, 2, 0, 4, 3, 5]
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

def faceClass : Fin 6 → Fin 3 := ![0, 0, 0, 1, 1, 2]
def faceRep : Fin 3 → Fin 6 := ![0, 3, 5]

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

noncomputable def vertexEquiv : M.Vertex ≃ Fin 2 :=
  OrbitClassifier.orbitEquiv M.sigma (![0, 1, 1, 1, 1, 1] : Fin 6 → Fin 2)
    (![0, 1] : Fin 2 → Fin 6) (by decide) (by decide) (by decide)

theorem planar : M.IsPlanar := by
  constructor
  · have hstep : ∀ d : Fin 6, Relation.EqvGen M.Adjacent 0 d := by
      have trans {d e f : M.Dart}
          (hde : Relation.EqvGen M.Adjacent d e)
          (hef : Relation.EqvGen M.Adjacent e f) :
          Relation.EqvGen M.Adjacent d f := .trans _ _ _ hde hef
      have h01 : Relation.EqvGen M.Adjacent 0 1 :=
        .rel _ _ (Or.inl rfl)
      have h12 : Relation.EqvGen M.Adjacent 1 2 :=
        .rel _ _ (Or.inr rfl)
      have h24 : Relation.EqvGen M.Adjacent 2 4 :=
        .rel _ _ (Or.inr rfl)
      have h45 : Relation.EqvGen M.Adjacent 4 5 :=
        .rel _ _ (Or.inl rfl)
      have h53 : Relation.EqvGen M.Adjacent 5 3 :=
        .rel _ _ (Or.inr rfl)
      intro d
      fin_cases d
      · exact .refl _
      · exact h01
      · exact trans h01 h12
      · exact trans (trans (trans (trans h01 h12) h24) h45) h53
      · exact trans (trans h01 h12) h24
      · exact trans (trans (trans h01 h12) h24) h45
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

def faceDarts : Fin 3 → List (Fin 6) := ![[0, 2, 1], [3, 4], [5]]

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

def a : G := Equiv.swap 1 2
def b : G := Equiv.swap 0 1

def D : RelGenSet G Empty where
  base := Set.univ
  fam := Empty.elim
  symmetricGenerating := by
    rw [Set.univ_union]
    exact ⟨fun _ _ => Set.mem_univ _, Subgroup.closure_univ⟩

def label (d : Fin 6) : RelLetter G Empty :=
  .base ((![b, b⁻¹, a, a⁻¹, a, a⁻¹] : Fin 6 → G) d)

def relator : List (RelLetter G Empty) := [.base b, .base a, .base b⁻¹]
def W : Set (List (RelLetter G Empty)) := {relator}

def relatorCell : RelatorCell M (face 2) W where
  face := face 0
  face_ne_outer := (face_eq_iff 0 2).not.mpr (by decide)
  word := relator
  word_mem := rfl
  conjugator := b⁻¹
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
  relatorCells := [relatorCell]
  relatorCell_faces_nodup := by simp
  relatorCell_word := by
    intro C hC
    have h : C = relatorCell := List.mem_singleton.mp hC
    subst C
    change relator = (boundary (face 0)).darts.map label
    rw [boundary_face_darts]
    rfl
  inner_face := by
    intro f hf
    obtain ⟨i, rfl⟩ : ∃ i, face i = f := ⟨faceEquiv f, faceEquiv.left_inv f⟩
    fin_cases i
    · exact Or.inl ⟨relatorCell, List.mem_singleton_self _, rfl⟩
    · right
      rw [boundary_face_darts]
      change a⁻¹ * (a * 1) = 1
      simp
    · exact (hf rfl).elim
  boundary_product := by
    rw [boundary_face_darts]
    change b⁻¹ * (b * (a * (b⁻¹ * 1))) * (b⁻¹)⁻¹ * 1 = (a⁻¹)⁻¹ * 1
    group

instance : NeZero diagram.rCellCount := ⟨by decide⟩
instance (n : ℕ) : OfNat diagram.toCombMap.Dart n := inferInstanceAs (OfNat (Fin 6) n)
instance : DecidableEq diagram.toCombMap.Dart := inferInstanceAs (DecidableEq (Fin 6))

@[simp] theorem diagram_boundaryWord : diagram.boundaryWord = [.base a] := by
  change RelWord.revInv ((boundary (face 2)).darts.map label) = _
  rw [boundary_face_darts]
  simp [faceDarts, label, RelWord.revInv, RelWord.inv]

@[simp] theorem diagram_cellDarts : Embedded.cellDarts diagram 0 = [0, 2, 1] := by
  change (boundary (face 0)).darts = _
  rw [boundary_face_darts]
  rfl

@[simp] theorem diagram_outerDarts : Embedded.outerDarts diagram = [4] := by
  change ((boundary (face 2)).darts.reverse.map M.alpha) = _
  rw [boundary_face_darts]
  rfl

def faces : Finset diagram.toCombMap.Face := {face 1}

theorem isBoundaryDart_iff (d : Fin 6) :
    Embedded.IsBoundaryDart diagram faces d ↔ d = 3 ∨ d = 4 := by
  change (M.faceOf d ∈ ({face 1} : Finset M.Face) ∧
    M.faceOf (M.alpha d) ∉ ({face 1} : Finset M.Face)) ↔ _
  simp only [Finset.mem_singleton, faceOf_eq_face]
  fin_cases d <;> decide

theorem step34 : Embedded.BoundaryStep diagram faces 3 4 :=
  ⟨(isBoundaryDart_iff 3).mpr (Or.inl rfl),
    (isBoundaryDart_iff 4).mpr (Or.inr rfl), .refl⟩

theorem step43 : Embedded.BoundaryStep diagram faces 4 3 :=
  ⟨(isBoundaryDart_iff 4).mpr (Or.inr rfl),
    (isBoundaryDart_iff 3).mpr (Or.inl rfl), .refl⟩

noncomputable def regionBoundary : Embedded.FaceSetBoundary diagram faces where
  faces_nonempty := Finset.singleton_nonempty _
  all_gCells := by
    intro f hf
    have h : f = face 1 := Finset.mem_singleton.mp hf
    subst f
    refine ⟨(face_eq_iff 1 2).not.mpr (by decide), ?_⟩
    change RelLetter.listVal ((boundary (face 1)).darts.map label) = 1
    rw [boundary_face_darts]
    change a⁻¹ * (a * 1) = 1
    simp
  cycle := [3, 4]
  cycle_nonempty := List.cons_ne_nil _ _
  cycle_nodup := by decide
  cycle_mem_iff := by
    intro d
    rw [isBoundaryDart_iff]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rfl
  cycle_chain := by
    simpa only [List.isChain_cons_cons, List.isChain_singleton, and_true] using step34
  cycle_closes := step43

def sourceArc : Embedded.CyclicArc (Embedded.cellDarts diagram 0) where
  start := ⟨1, by rw [diagram_cellDarts]; decide⟩
  length := 1
  length_le := by rw [diagram_cellDarts]; decide

def targetArc : Embedded.CyclicArc (Embedded.targetDarts diagram none) where
  start := ⟨0, Nat.zero_lt_succ _⟩
  length := 1
  length_le := by change 1 ≤ (Embedded.outerDarts diagram).length; rw [diagram_outerDarts]; decide

noncomputable def region : Embedded.Contiguity D 0 diagram faces where
  boundary := regionBoundary
  source := 0
  target := none
  sourceArc := sourceArc
  targetArc := targetArc
  rightSide := []
  leftSide := []
  boundary_decomposition := by
    change [3, 4] = sourceArc.reverseDarts ++ [] ++ targetArc.darts ++ []
    simp only [Embedded.CyclicArc.reverseDarts, Embedded.CyclicArc.darts,
      Embedded.CyclicArc.rotated, sourceArc, targetArc, Embedded.targetDarts,
      diagram_cellDarts, diagram_outerDarts]
    rfl
  rightSide_length_le := le_rfl
  leftSide_length_le := le_rfl
  rightSide_norm_le := by change wordNorm D.alphabet.carrier 1 ≤ 0; rw [wordNorm_one]
  leftSide_norm_le := by change wordNorm D.alphabet.carrier 1 ≤ 0; rw [wordNorm_one]
  target_ne_source := by intro i h; cases h
  o52Certificate := by intro i h; cases h
  pasting := by
    refine ⟨[face 1], ?_⟩
    have h := Embedded.shelling_oneFace (Delta := diagram) (faces := faces)
      (face := face 1) (Finset.mem_singleton_self _) 0
    rw [List.rotate_zero] at h
    change Embedded.FaceShelling diagram faces [face 1] ((boundary (face 1)).darts) at h
    rw [boundary_face_darts] at h
    exact h

noncomputable def exteriorRegion : EmbeddedBoundaryContiguity D 0 diagram 0 where
  faces := faces
  region := region
  source_eq := rfl
  target_eq := rfl

/-- No nonempty prefix of the fixed relator has the value of an outer arc. -/
theorem prefix_values : ∀ n : Fin 4, 1 ≤ n.val →
    RelLetter.listVal (relator.take n.val) ≠ 1 ∧
      RelLetter.listVal (relator.take n.val) ≠ a := by decide

/-- The algebraic target cannot contain even one exterior letter in this
example, although the embedded region has a one-letter exterior arc. -/
theorem no_nonempty_based_contiguity
    (C : RelativeBoundaryContiguity D 0 [a] relator) :
    ¬ 1 ≤ C.exterior.length := by
  intro hpos
  have hleft : C.leftSide = [] := List.length_eq_zero_iff.mp
    (Nat.eq_zero_of_le_zero C.leftSide_short)
  have hright : C.rightSide = [] := List.length_eq_zero_iff.mp
    (Nat.eq_zero_of_le_zero C.rightSide_short)
  have harc : C.boundaryArc.prod = 1 ∨ C.boundaryArc.prod = a := by
    cases hword : C.boundaryArc with
    | nil => exact Or.inl rfl
    | cons x xs =>
      have hx : x = a := by
        have hmem : x ∈ C.boundaryArc := by rw [hword]; exact List.mem_cons_self
        simpa only [List.mem_singleton] using C.boundaryArc_mem_boundaryWord hmem
      have hlen := C.boundaryArc_length_le_boundaryWord
      rw [hword] at hlen
      have hxs : xs = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
      right
      simp [hx, hxs]
  have hlen := C.exterior_length_le_relator
  have hn : C.exterior.length < 4 := by
    change C.exterior.length ≤ 3 at hlen
    omega
  have hprefix := prefix_values ⟨C.exterior.length, hn⟩ hpos
  have htake : relator.take C.exterior.length = C.exterior := by
    calc
      relator.take C.exterior.length =
          (C.exterior ++ C.remainder).take C.exterior.length :=
        congrArg (List.take C.exterior.length) C.relator_decomposition
      _ = C.exterior := List.take_left
  change RelLetter.listVal (relator.take C.exterior.length) ≠ 1 ∧
    RelLetter.listVal (relator.take C.exterior.length) ≠ a at hprefix
  rw [htake] at hprefix
  have hvalue := C.exterior_value
  rw [hleft, hright, RelLetter.listVal_nil, one_mul, mul_one] at hvalue
  rcases harc with harc | harc
  · exact hprefix.1 (hvalue.trans harc)
  · exact hprefix.2 (hvalue.trans harc)

/-- A concrete input to the exterior-arc conversion with no possible output.
This uses the supplied-word statement's exact boundary and relator equalities. -/
theorem exterior_arc_conversion_counterexample :
    diagram.boundaryWord = [RelLetter.base a] ∧
      ([RelLetter.base a] : List (RelLetter G Empty)).map RelLetter.val = [a] ∧
      (Embedded.cell diagram 0).word = relator ∧
      ¬ ∃ C : RelativeBoundaryContiguity D 0 [a] relator,
        exteriorRegion.region.sourceArc.length ≤ C.exterior.length := by
  refine ⟨diagram_boundaryWord, rfl, rfl, ?_⟩
  rintro ⟨C, hC⟩
  exact no_nonempty_based_contiguity C hC

/-- The supplied-word exterior-arc conversion is false for a fixed based
relator.  The source cyclic arc must be allowed to rebase that relator. -/
theorem not_relativeExteriorArcConversionAtWordStatement :
    ¬ RelativeExteriorArcConversionAtWordStatement.{0, 0} := by
  intro h
  obtain ⟨C, hC⟩ := h D 0 diagram [a] [.base a]
    diagram_boundaryWord rfl 0 exteriorRegion relator rfl
  exact no_nonempty_based_contiguity C hC

#audit_closed_axioms exterior_arc_conversion_counterexample
#audit_closed_axioms not_relativeExteriorArcConversionAtWordStatement

end GroupApproximation.GGT.VanKampen.ExteriorArcCounterexample
