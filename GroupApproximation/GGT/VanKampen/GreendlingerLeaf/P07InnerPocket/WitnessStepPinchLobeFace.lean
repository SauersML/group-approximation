import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepPinchLobeStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepPinchOffProof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepPinchCutProof
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-55: curve entries with face in `F` are on the walk

Lane gl-p07-55.  Certifies no printed sentence on its own.  NOT COMPILED.

* `witnessStepPinchLobe_not_both`: in a list without duplicates, `y` before `x` and `x` before
  `y` cannot both hold.
* `witnessStepPinchLobe_alpha_mem_pieces`: `α` of a curve entry is a dart of a piece of `Γ`.
* `witnessStepPinchLobe_faces`: the four face facts of the premise block.
* `witnessStepPinchLobe_mem_of_faceOf_mem`: a curve entry whose face is in `F` lies in
  `invDarts X ow`.

See `WitnessStepPinchLobeStatement.lean` for the route, the truth check and the LOUD notes.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

/-- **Two orders cannot both hold** in a list without duplicates. -/
theorem witnessStepPinchLobe_not_both {β : Type*} {L p m q u v z : List β} {x y : β}
    (hL : L.Nodup) (h1 : L = p ++ y :: (m ++ x :: q)) (h2 : L = u ++ x :: (v ++ y :: z)) :
    False := by
  have e1 : (p ++ y :: m) ++ x :: q = u ++ x :: (v ++ y :: z) :=
    (by simp : (p ++ y :: m) ++ x :: q = p ++ y :: (m ++ x :: q)).trans (h1.symm.trans h2)
  have e2 : (u ++ x :: v) ++ y :: z = p ++ y :: (m ++ x :: q) :=
    (by simp : (u ++ x :: v) ++ y :: z = u ++ x :: (v ++ y :: z)).trans (h2.symm.trans h1)
  have n1 : ((p ++ y :: m) ++ x :: q).Nodup := by
    rw [e1, ← h2]
    exact hL
  have n2 : ((u ++ x :: v) ++ y :: z).Nodup := by
    rw [e2, ← h1]
    exact hL
  obtain ⟨hu, -⟩ := WitnessCurveSublistList.append_cons_inj_of_nodup n1 e1
  obtain ⟨hp, -⟩ := WitnessCurveSublistList.append_cons_inj_of_nodup n2 e2
  have l1 := congrArg List.length hu
  have l2 := congrArg List.length hp
  simp only [List.length_append, List.length_cons] at l1 l2
  omega

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinchLobe_not_both

section PinchLobeFace

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **`α` of a curve entry is a dart of a piece of `Γ`.** -/
theorem witnessStepPinchLobe_alpha_mem_pieces {a b : RegionCandidate D eps X}
    {G₁ : CyclicArc (cellDarts X i)} {G₂ : CyclicArc (cellDarts X j)} {t : X.toCombMap.Dart}
    (ht : t ∈ witnessSublistCurve a b G₁ G₂) :
    X.toCombMap.alpha t ∈ G₁.darts ∨ X.toCombMap.alpha t ∈ b.sideFrom i ∨
      X.toCombMap.alpha t ∈ G₂.darts ∨ X.toCombMap.alpha t ∈ a.sideFrom j := by
  unfold witnessSublistCurve at ht
  rcases List.mem_append.mp ht with h | h4
  · rcases List.mem_append.mp h with h | h3
    · rcases List.mem_append.mp h with h1 | h2
      · exact Or.inl (witnessStepCorner_alpha_mem_of_mem_invDarts h1)
      · unfold FourBlock.sideAWord at h2
        exact Or.inr (Or.inr (Or.inr
          (witnessStepCorner_alpha_mem_of_mem_invDarts (List.mem_filter.mp h2).1)))
    · exact Or.inr (Or.inr (Or.inl
        (witnessStepCorner_alpha_mem_of_mem_invDarts (FourBlock.mem_cellG2Word h3).2)))
  · exact Or.inr (Or.inl (FourBlock.mem_sideBWord h4).2.2)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinchLobe_alpha_mem_pieces

/-- **The four face facts of the premise block**: the witness faces are off `a`, off `b`, and do
not contain the faces of `Π_i` and `Π_j`. -/
theorem witnessStepPinchLobe_faces {a b : RegionCandidate D eps X}
    {K : CellPocketWalk D eps X i j} {c : X.toCombMap.Face}
    (hw : IsNoncrossingClosedWalk X.toCombMap K.walk) (hca : c ∉ a.1) (hcb : c ∉ b.1) :
    (∀ f ∈ witnessFaces a b K c, f ∉ a.1) ∧ (∀ f ∈ witnessFaces a b K c, f ∉ b.1) ∧
      (cell X i).face ∉ witnessFaces a b K c ∧ (cell X j).face ∉ witnessFaces a b K c :=
  ⟨fun _ hf => not_mem_left_of_mem_witnessFaces hca hf,
    fun _ hf => not_mem_right_of_mem_witnessFaces hcb hf,
    fun hf => PocketClass.cell_face_not_mem_sideFaces hw K.firstArc K.firstArc_pos
      (fun _ hd => PocketClass.mem_walk_of_mem_invDarts_firstArc K hd)
      (witnessFaces_subset_sideFaces hf),
    fun hf => PocketClass.cell_face_not_mem_sideFaces hw K.secondArc K.secondArc_pos
      (fun _ hd => PocketClass.mem_walk_of_mem_invDarts_secondArc K hd)
      (witnessFaces_subset_sideFaces hf)⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinchLobe_faces

/-- **A curve entry with face in `F` is on the inverted enclosing walk.**  `α t` is on a piece of
`Γ`, so its face is off `F`; and across it lies `faceOf t ∈ F`, so `α t ∈ ow` by `mem_iff`. -/
theorem witnessStepPinchLobe_mem_of_faceOf_mem {a b : RegionCandidate D eps X}
    {G₁ : CyclicArc (cellDarts X i)} {G₂ : CyclicArc (cellDarts X j)}
    {F : Finset X.toCombMap.Face} {ow : List X.toCombMap.Dart} (E : EnclosedFaceSetSucc X F ow)
    (hFa : ∀ f ∈ F, f ∉ a.1) (hFb : ∀ f ∈ F, f ∉ b.1)
    (hFi : (cell X i).face ∉ F) (hFj : (cell X j).face ∉ F) {t : X.toCombMap.Dart}
    (ht : t ∈ witnessSublistCurve a b G₁ G₂) (hF : X.toCombMap.faceOf t ∈ F) :
    t ∈ invDarts X ow := by
  apply witnessStepCorner_mem_invDarts_of_alpha_mem
  have hα : X.toCombMap.faceOf (X.toCombMap.alpha t) ∉ F :=
    witnessStepPinchOff_faceOf_not_mem hFa hFb hFi hFj (witnessStepPinchLobe_alpha_mem_pieces ht)
  refine (E.mem_iff _).mpr ⟨hα, Or.inl ?_⟩
  rw [X.toCombMap.alpha_involutive t]
  exact hF

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinchLobe_mem_of_faceOf_mem

end PinchLobeFace

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
