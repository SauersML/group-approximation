import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPinchPosModelsDiagram
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPinchPosModelsNoRescue
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPinchPositive
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketFullArc
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketRegionOfSimple
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketOuterPart
import GroupApproximation.GGT.VanKampen.FaceShellingValue
import GroupApproximation.GGT.VanKampen.GRegionBoundaryValue
import GroupApproximation.GGT.VanKampen.SurgeryCutRecord
import GroupApproximation.Meta.AxiomGuard

/-!
# The positive pinch fails at `ε = 1`

`PocketPinchLabelledPosStatement` (`Estimating/OsinPocketPinchPositive.lean`) repairs the pinch of
Osin's Lemma 9.7(b) at `ε = 0` by the binder `0 < eps`.  This module shows the repaired statement is
still false, at `ε = 1`.
* The diagram `pinchDiagram` (`OsinPocketPinchPosModelsDiagram`) has letter labels and a pocket face
  set `pinchK` in walk order between the positions `0` and `1`.
* No O-equivalent copy has a simple pocket face set between those positions.

Let `X'` be an O-equivalent copy with a simple pocket face set `K'`.  An O-equivalence keeps the
boundary word `c` and the relator words `P = a a b` and `Q = d d e`.
* **The target arc is empty.**  Otherwise it is all of `∂X'`.  A pocket with a full target arc is not
  simple, unless its cycle is that one dart, and then every face lies in the face set or is the
  exterior (`PocketWrap.eq_or_mem_of_cycle_eq_singleton`).
* **The source arc is proper.**  Otherwise the cycle is the reversed boundary of the source cell,
  and every face is that cell or lies in the face set (`eq_or_mem_of_cycle_mem_iff`).
* **The relation.**  The cycle `s_1 t_1⁻¹ s_2` is a simple closed walk, so its side is a pocket region
  whose van Kampen diagram has exactly one relator cell.  That cell is the kept cell, whose word is
  the relator other than the source word.  So `α · p⁻¹ · β = g r^{±1} g⁻¹`, with `α` and `β` the
  side values of word norm at most one, `p` a proper cyclic arc of the source word and `r` the other
  relator.  `noRescueKeptQ` and `noRescueKeptP` (`OsinPocketPinchPosModelsNoRescue`) refute it.

* `pocketPinchPosRefutation : ¬ PocketPinchLabelledPosStatement.{0, 0, 0}`.

The section form `PocketPinchLabelledSectionStatement` quantifies over families satisfying
`C(ε, μ, λ, c, ρ)` beyond thresholds, whose relators are long, so this diagram does not touch it.

## Manuscript status

Model test for infrastructure of `thm:hull` (Hull's small cancellation theorem, through Osin's
Lemma 9.7(b)); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.OsinPocketPinchPosModels

open GGT Embedded
open Surgery.MapCollapse (IsBoundaryDart BoundaryCycle)

/-! ## Closure and letters -/

/-- **A boundary cycle made of the reversed darts of a face closes up the face set.**  If a dart lies
on the cycle exactly when its reversal lies on the boundary of `g`, then every face of a connected
map is `g` or lies in the face set. -/
theorem eq_or_mem_of_cycle_mem_iff {M : CombMap.{0}} (hM : M.IsConnected)
    {faces : Finset M.Face} (K : BoundaryCycle M faces) {g : M.Face} (B : FaceBoundary M g)
    (hmem : ∀ d, d ∈ K.cycle ↔ M.alpha d ∈ B.darts) (f : M.Face) : f = g ∨ f ∈ faces := by
  refine PocketWrap.forall_face_of_alpha_closed M hM (fun f => f = g ∨ f ∈ faces) ?_
    (d₀ := B.darts.head B.nonempty) (Or.inl ((B.mem_iff _).mp (List.head_mem B.nonempty))) f
  intro d hd
  change M.faceOf d = g ∨ M.faceOf d ∈ faces at hd
  rcases hd with hdg | hdf
  · have hdB : d ∈ B.darts := (B.mem_iff d).mpr hdg
    have hb : IsBoundaryDart M faces (M.alpha d) :=
      (K.cycle_mem_iff (M.alpha d)).mp ((hmem _).mpr (by rwa [M.alpha_involutive d]))
    exact Or.inr hb.1
  · by_cases hout : M.faceOf (M.alpha d) ∈ faces
    · exact Or.inr hout
    · have hdK : d ∈ K.cycle := (K.cycle_mem_iff d).mpr ⟨hdf, hout⟩
      exact Or.inl ((B.mem_iff _).mp ((hmem d).mp hdK))

/-- An element of word norm at most one is `1` or a base letter. -/
theorem mem_T_of_wordNorm_le_one {g : G} (h : WordMetric.wordNorm D.alphabet.carrier g ≤ 1) :
    g ∈ T := by
  obtain ⟨l, hl, hlen⟩ := WordMetric.exists_isWord_length_eq D.alphabet.symmetricGenerating g
  have hl1 : l.length ≤ 1 := hlen.trans_le h
  rcases l with _ | ⟨x, _ | ⟨y, t⟩⟩
  · have hg : g = 1 := hl.prod_eq.symm.trans List.prod_nil
    rw [hg]
    exact Set.mem_insert 1 baseSet
  · have hx : x ∈ D.alphabet.carrier := hl.letters x (List.mem_singleton_self x)
    have hg : g = x := hl.prod_eq.symm.trans List.prod_singleton
    rw [hg]
    rcases hx with hx | hx
    · exact Set.mem_insert_of_mem 1 hx
    · exact (Set.mem_iUnion.mp hx).elim fun e _ => e.elim
  · simp only [List.length_cons] at hl1
    omega

/-- The relators have values other than `1`. -/
theorem listVal_ne_one_of_mem_pinchW {w : List (RelLetter G Empty)} (hw : w ∈ pinchW) :
    RelLetter.listVal w ≠ 1 := by
  rcases hw with rfl | rfl
  · rw [listVal_pWord]
    intro h
    have hA := congrArg (fun z => Multiplicative.toAdd (expA z)) h
    simp only [expA_gP, map_one, toAdd_one] at hA
    omega
  · rw [listVal_qWord]
    intro h
    have hD := congrArg (fun z => Multiplicative.toAdd (expD z)) h
    simp only [expD_gQ, map_one, toAdd_one] at hD
    omega

/-- The relator words of the diagram, by index. -/
theorem pinchDiagram_cell_word_cases (k : Fin pinchDiagram.rCellCount) :
    ((cell pinchDiagram k).word = pWord ∧ k.val = 0) ∨
      ((cell pinchDiagram k).word = qWord ∧ k.val = 1) := by
  obtain ⟨n, hn⟩ := k
  have hn2 : n < 2 := hn
  interval_cases n
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

/-! ## No simple copy -/

/-- **No O-equivalent copy of the counterexample has a simple pocket face set between the positions
`0` and `1` at `ε = 1`.** -/
theorem false_of_simple {X' : DiscDiagram.{0, 0, 0} pinchW}
    (e : OEquivalentDiscDiagram pinchDiagram X') (K' : PocketFaceSet D 1 X' 0 1)
    (hsimple : K'.Simple) : False := by
  have hconn : X'.toCombMap.IsConnected := X'.toCombMap.connected_of_planar X'.planar
  have hcount : X'.rCellCount = 2 := e.rCellCount_eq
  have hword : ∀ k : Fin X'.rCellCount,
      (cell X' k).word = (cell pinchDiagram (e.cellIndex.symm k)).word := by
    intro k
    have h := e.cellWord_eq (e.cellIndex.symm k)
    rwa [Equiv.apply_symm_apply] at h
  have hlen3 : ∀ k : Fin X'.rCellCount, (cellDarts X' k).length = 3 := by
    intro k
    rw [PocketWrap.cellDarts_length_eq_word_length, hword]
    rcases pinchDiagram_cell_word_cases (e.cellIndex.symm k) with ⟨h, -⟩ | ⟨h, -⟩ <;>
      rw [h] <;> rfl
  -- The exterior face has one dart.
  have houterLen : (X'.faceBoundary X'.outerFace).darts.length = 1 := by
    rw [PocketWrap.outerBoundary_darts_length, e.boundaryWord_eq, pinchDiagram_boundaryWord]
    rfl
  obtain ⟨o, ho⟩ := List.length_eq_one_iff.mp houterLen
  have hout1 : outerDarts X' = [X'.toCombMap.alpha o] := by
    change (X'.faceBoundary X'.outerFace).darts.reverse.map X'.toCombMap.alpha = _
    rw [ho]
    rfl
  -- The target arc is empty.
  have htl : K'.targetArc.darts.length ≤ 1 :=
    K'.targetArc.darts_length.trans_le
      (K'.targetArc.length_le.trans_eq ((congrArg List.length hout1).trans List.length_singleton))
  have htgt : ∀ d ∈ K'.targetArc.darts, d = X'.toCombMap.alpha o := fun d hd => by
    have h := K'.targetArc.mem_cycle_of_mem_darts hd
    rw [hout1, List.mem_singleton] at h
    exact h
  have ht2 : K'.targetArc.darts = [] := by
    rcases PocketWrap.eq_nil_or_eq_singleton htl htgt with h | h
    · exact h
    · exfalso
      by_cases hrest : K'.firstSide ++ invDarts X' K'.sourceArc.darts ++ K'.secondSide = []
      · have hC : K'.boundary.cycle = [X'.toCombMap.alpha o] := by
          rw [K'.decomposition, hrest, h, List.nil_append]
        rcases PocketWrap.eq_or_mem_of_cycle_eq_singleton hconn K'.boundary
            (X'.faceBoundary X'.outerFace) ho hC (cell X' K'.source).face with hf | hf
        · exact (cell X' K'.source).face_ne_outer hf
        · exact K'.source_not_mem hf
      · refine PocketFaceSet.not_simple_of_full_targetArc K' ?_ hrest hsimple
        rw [← K'.targetArc.darts_length, h, hout1]
  -- The source arc is proper.
  have hsl : K'.sourceArc.length ≤ 3 := K'.sourceArc.length_le.trans_eq (hlen3 K'.source)
  have hn : K'.sourceArc.length < 3 := by
    refine lt_of_le_of_ne hsl fun hfull => ?_
    have hfull' : K'.sourceArc.length = (cellDarts X' K'.source).length :=
      hfull.trans (hlen3 K'.source).symm
    by_cases hrest : K'.firstSide ++ K'.secondSide ++ K'.targetArc.darts = []
    · have hs₁ : K'.firstSide = [] :=
        (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp hrest).1).1
      have hs₂ : K'.secondSide = [] :=
        (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp hrest).1).2
      have hdarts := PocketFullArc.darts_eq_rotate_of_full K'.sourceArc hfull'
      have hmemC : ∀ d, d ∈ K'.boundary.cycle ↔
          X'.toCombMap.alpha d ∈ (X'.faceBoundary (cell X' K'.source).face).darts := by
        intro d
        rw [K'.decomposition, hs₁, hs₂, ht2, hdarts]
        simp only [List.nil_append, List.append_nil, invDarts, List.mem_map, List.mem_reverse,
          List.mem_rotate]
        constructor
        · rintro ⟨x, hx, rfl⟩
          rwa [X'.toCombMap.alpha_involutive]
        · intro hd
          exact ⟨_, hd, X'.toCombMap.alpha_involutive d⟩
      rcases eq_or_mem_of_cycle_mem_iff hconn K'.boundary
          (X'.faceBoundary (cell X' K'.source).face) hmemC X'.outerFace with hf | hf
      · exact (cell X' K'.source).face_ne_outer hf.symm
      · exact K'.outerFace_not_mem hf
    · exact PocketFaceSet.not_simple_of_full_sourceArc K' hfull' hrest hsimple
  -- The side of the simple cycle is a pocket region.
  have hS : IsSimpleClosedWalk X'.toCombMap K'.boundary.cycle := hsimple
  have hside : SimpleClosedWalkSides.sideFaces X'.toCombMap K'.boundary.cycle = K'.faces :=
    K'.sideFaces_boundary_cycle_eq_faces
  obtain ⟨P, hPfaces, hPouter⟩ : ∃ P : PocketRegion X',
      P.faces = K'.faces ∧ invDarts X' P.outer.cycle = K'.boundary.cycle :=
    ⟨PocketRegion.ofSimpleClosedWalk hS (K'.outerFace_not_mem_sideFaces hside),
      (PocketRegion.ofSimpleClosedWalk_faces hS (K'.outerFace_not_mem_sideFaces hside)).trans
        hside,
      PocketRegion.ofSimpleClosedWalk_invDarts_outer hS (K'.outerFace_not_mem_sideFaces hside)⟩
  -- The van Kampen diagram of the pocket has one relator cell.
  have hcells1 : P.diagram.rCellCount ≤ 1 := by
    refine P.diagram_rCellCount_le.trans (Nat.le_of_lt_succ ?_)
    refine lt_of_lt_of_eq (List.length_filter_lt_length_iff_exists.mpr
      ⟨cell X' K'.source, cell_mem X' K'.source, ?_⟩) hcount
    simpa [hPfaces] using K'.source_not_mem
  have hpos : 0 < P.diagram.rCellCount :=
    P.diagram_rCellCount_pos (cell_mem X' K'.kept) (by rw [hPfaces]; exact K'.kept_mem)
  obtain ⟨C, hCs⟩ := List.length_eq_one_iff.mp (le_antisymm hcells1 (Nat.succ_le_of_lt hpos))
  have hmemC : C ∈ P.diagram.relatorCells := by
    rw [show P.diagram.relatorCells = [C] from hCs]
    exact List.mem_singleton_self C
  -- Its word is the word of a relator cell of `X'` inside the face set.
  obtain ⟨g, hg, hgC⟩ := Surgery.MapCollapse.exists_keptFace_of_ne_newFace X'.toCombMap P.outside
    P.outer C.face C.face_ne_outer
  have hCword : C.word = X'.faceWord g := by
    have h := P.diagram.relatorCell_word C hmemC
    rw [hgC] at h
    exact h.trans (Surgery.MapCollapse.replaceGRegionFaceBoundary_keptFace_word X' P.outside P.outer
      g hg)
  have hgP : g ∈ P.faces := P.mem_faces_of_not_mem_outside hg
  have hgo : g ≠ X'.outerFace := fun h => hg (h ▸ P.outerFace_mem)
  have hfw : X'.faceWord g ∈ pinchW := by
    rw [← hCword]
    exact C.word_mem
  rcases X'.inner_face g hgo with ⟨C', hC', hC'g⟩ | hone
  swap
  · exact listVal_ne_one_of_mem_pinchW hfw hone
  obtain ⟨k, hk⟩ := List.get_of_mem hC'
  have hkword : C.word = (cell X' k).word := by
    rw [hCword, show cell X' k = C' from hk, X'.relatorCell_word C' hC', hC'g]
    rfl
  have hks : k ≠ K'.source := fun h => K'.source_not_mem (by
    rw [← hPfaces, ← h, show cell X' k = C' from hk, hC'g]
    exact hgP)
  have hsymm : e.cellIndex.symm k ≠ e.cellIndex.symm K'.source :=
    fun h => hks (e.cellIndex.symm.injective h)
  -- The relation.
  have hval : RelatorCell.value C = RelLetter.listVal (dartWord X' K'.firstSide) *
      (RelLetter.listVal (dartWord X' K'.sourceArc.darts))⁻¹ *
        RelLetter.listVal (dartWord X' K'.secondSide) := by
    have h := P.diagram.boundary_product
    change _ = RelLetter.listVal P.diagram.boundaryWord at h
    rw [PocketRegion.diagram_boundaryWord, hPouter, K'.decomposition, ht2, List.append_nil,
      Embedded.dartWord_append, Embedded.dartWord_append, HullSC.RelWord.listVal_append,
      HullSC.RelWord.listVal_append, Embedded.listVal_dartWord_invDarts,
      show P.diagram.relatorCells = [C] from hCs] at h
    simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] using h
  have harc : dartWord X' K'.sourceArc.darts =
      ((cell X' K'.source).word.rotate K'.sourceArc.start.1).take K'.sourceArc.length := by
    rw [CyclicArc.darts, CyclicArc.rotated_eq_rotate, ← dartWord_cellDarts]
    simp only [dartWord, List.map_take, List.map_rotate]
  have hα : RelLetter.listVal (dartWord X' K'.firstSide) ∈ T :=
    mem_T_of_wordNorm_le_one K'.firstSide_norm_le
  have hβ : RelLetter.listVal (dartWord X' K'.secondSide) ∈ T :=
    mem_T_of_wordNorm_le_one K'.secondSide_norm_le
  rcases pinchDiagram_cell_word_cases (e.cellIndex.symm K'.source) with ⟨hsrc, hs0⟩ | ⟨hsrc, hs1⟩
  · -- Source word `P`, kept word `Q`.
    have hkq : (cell pinchDiagram (e.cellIndex.symm k)).word = qWord := by
      rcases pinchDiagram_cell_word_cases (e.cellIndex.symm k) with ⟨-, hk0⟩ | ⟨h, -⟩
      · exact absurd (Fin.ext (hk0.trans hs0.symm)) hsymm
      · exact h
    have hconj : RelatorCell.value C =
        C.conjugator * (if !C.reversed then gQ else gQ⁻¹) * C.conjugator⁻¹ := by
      unfold RelatorCell.value
      rw [hkword, hword k, hkq, listVal_qWord]
      rcases C.reversed with _ | _ <;> rfl
    rw [harc, hword K'.source, hsrc] at hval
    exact noRescueKeptQ hα hβ hn (!C.reversed) (hval.symm.trans hconj)
  · -- Source word `Q`, kept word `P`.
    have hkp : (cell pinchDiagram (e.cellIndex.symm k)).word = pWord := by
      rcases pinchDiagram_cell_word_cases (e.cellIndex.symm k) with ⟨h, -⟩ | ⟨-, hk1⟩
      · exact h
      · exact absurd (Fin.ext (hk1.trans hs1.symm)) hsymm
    have hconj : RelatorCell.value C =
        C.conjugator * (if !C.reversed then gP else gP⁻¹) * C.conjugator⁻¹ := by
      unfold RelatorCell.value
      rw [hkword, hword k, hkp, listVal_pWord]
      rcases C.reversed with _ | _ <;> rfl
    rw [harc, hword K'.source, hsrc] at hval
    exact noRescueKeptP hα hβ hn (!C.reversed) (hval.symm.trans hconj)

/-! ## The endpoint -/

/-- **The positive pinch fails at the universes `0, 0, 0`**, witnessed by `pinchK` at `ε = 1`. -/
def PocketPinchPosRefutation : Prop :=
  ¬ PocketPinchLabelledPosStatement.{0, 0, 0}

theorem pocketPinchPosRefutation : PocketPinchPosRefutation := by
  intro h
  obtain ⟨X', K', ⟨e⟩, hsimple⟩ :=
    h D 1 Nat.one_pos pinchW pinchDiagram 0 1 pinchDiagram_letters pinchK pinchK_closedWalk
  exact false_of_simple e K' hsimple

#audit_axioms eq_or_mem_of_cycle_mem_iff
#audit_axioms mem_T_of_wordNorm_le_one
#audit_axioms false_of_simple
#audit_closed_axioms pocketPinchPosRefutation

end GroupApproximation.GGT.VanKampen.OsinPocketPinchPosModels
