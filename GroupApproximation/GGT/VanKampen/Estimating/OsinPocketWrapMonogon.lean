import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPinchStep
import GroupApproximation.Meta.AxiomGuard

/-!
# The wrap case of the pinch, on monogons

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  In the wrap case the boundary cycle of the pocket follows the boundary
and is pinched, and the arc `t_1` is all of `∂Π` or the arc `t_2` is all of `∂X`.

This file shows that the pinch Props fail at `ε = 0` on a diagram whose relator words and boundary
word all have length one.  There the sides `s_1` and `s_2` are empty, and each arc has at most one
dart.  A pocket face set of such a diagram is never simple (`PocketWrap.not_simple_of_monogons`).

* With both arcs empty the boundary cycle is empty.
* With one arc empty the boundary cycle is the reversal of the only dart of a monogon, the source
  cell or the exterior face.  The face set and that monogon then hold every face
  (`PocketWrap.eq_or_mem_of_cycle_eq_singleton`), so the other monogon lies in the face set.
* With both arcs of one dart the dart of `t_1` is a loop, so `t_2` starts where `t_1` starts.

An O-equivalence keeps the lengths of the relator words and of the boundary word, so no
O-equivalent copy has a simple pocket face set at `ε = 0`
(`PocketWrap.no_simple_of_oEquivalent_monogons`).  So a pocket face set of such a diagram refutes
`PocketPinchStatement` and `PocketPinchPinchedStatement`, and one in walk order, with letter
labels, refutes `PocketPinchLabelledStatement` and `PocketPinchStepStatement`.
`Estimating/OsinPocketWrapRose.lean` has a diagram with these data.

## Manuscript status

Model test for infrastructure of `thm:hull` (tex 1903,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded Surgery.MapCollapse

namespace PocketWrap

/-- A rotation step from a dart lands in the face of its reversal. -/
theorem faceOf_sigma_eq_faceOf_alpha (M : CombMap.{v}) (d : M.Dart) :
    M.faceOf (M.sigma d) = M.faceOf (M.alpha d) := by
  have h : M.facePerm (M.alpha d) = M.sigma d := by
    change M.sigma (M.alpha (M.alpha d)) = M.sigma d
    rw [M.alpha_involutive d]
  rw [← h, M.faceOf_facePerm]

/-- A property of faces that holds at the face of one dart, and passes from the face of each dart
to the face of its reversal, holds at every face of a connected map. -/
theorem forall_face_of_alpha_closed (M : CombMap.{v}) (hM : M.IsConnected)
    (P : M.Face → Prop) (hP : ∀ d, P (M.faceOf d) → P (M.faceOf (M.alpha d)))
    {d₀ : M.Dart} (hd₀ : P (M.faceOf d₀)) (f : M.Face) : P f := by
  have hswap : ∀ d, P (M.faceOf d) ↔ P (M.faceOf (M.alpha d)) := fun d =>
    ⟨hP d, fun h => by
      have h' := hP (M.alpha d) h
      rwa [M.alpha_involutive d] at h'⟩
  have hall : ∀ d e, Relation.EqvGen M.Adjacent d e → (P (M.faceOf d) ↔ P (M.faceOf e)) := by
    intro d e h
    induction h with
    | rel x y hxy =>
      rcases (hxy : M.alpha x = y ∨ M.sigma x = y) with rfl | rfl
      · exact hswap x
      · rw [faceOf_sigma_eq_faceOf_alpha]
        exact hswap x
    | refl _ => exact Iff.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  obtain ⟨e, rfl⟩ := Quotient.mk''_surjective f
  exact (hall d₀ e (hM d₀ e)).mp hd₀

/-- The only dart of a one-dart face is a fixed point of the face permutation. -/
theorem facePerm_eq_self_of_darts_eq {M : CombMap.{v}} {f : M.Face} (B : FaceBoundary M f)
    {x : M.Dart} (hx : B.darts = [x]) : M.facePerm x = x := by
  have hxf : M.faceOf x = f := (B.mem_iff x).mp (by rw [hx]; exact List.mem_singleton_self x)
  have h : M.facePerm x ∈ B.darts := (B.mem_iff _).mpr ((M.faceOf_facePerm x).trans hxf)
  rw [hx] at h
  exact List.mem_singleton.mp h

/-- **A one-dart boundary cycle closes up the face set.**  If the boundary cycle of `faces` is the
reversal of the only dart `z` of a face `g`, then every face of a connected map is `g` or lies in
`faces`. -/
theorem eq_or_mem_of_cycle_eq_singleton {M : CombMap.{v}} (hM : M.IsConnected)
    {faces : Finset M.Face} (K : BoundaryCycle M faces) {g : M.Face} (B : FaceBoundary M g)
    {z : M.Dart} (hz : B.darts = [z]) (hK : K.cycle = [M.alpha z]) (f : M.Face) :
    f = g ∨ f ∈ faces := by
  have hzg : M.faceOf z = g := (B.mem_iff z).mp (by rw [hz]; exact List.mem_singleton_self z)
  refine forall_face_of_alpha_closed M hM (fun f => f = g ∨ f ∈ faces) ?_ (Or.inl hzg) f
  intro d hd
  change M.faceOf d = g ∨ M.faceOf d ∈ faces at hd
  rcases hd with hdg | hdf
  · have hdB : d ∈ B.darts := (B.mem_iff d).mpr hdg
    rw [hz, List.mem_singleton] at hdB
    rw [hdB]
    have hb : IsBoundaryDart M faces (M.alpha z) :=
      (K.cycle_mem_iff (M.alpha z)).mp (by rw [hK]; exact List.mem_singleton_self _)
    exact Or.inr hb.1
  · by_cases hout : M.faceOf (M.alpha d) ∈ faces
    · exact Or.inr hout
    · have hdK : d ∈ K.cycle := (K.cycle_mem_iff d).mpr ⟨hdf, hout⟩
      rw [hK, List.mem_singleton] at hdK
      rw [hdK, M.alpha_involutive z]
      exact Or.inl hzg

/-- A list of length at most one whose entries are all `x` is empty or `[x]`. -/
theorem eq_nil_or_eq_singleton {α : Type*} {l : List α} {x : α} (hlen : l.length ≤ 1)
    (hmem : ∀ d ∈ l, d = x) : l = [] ∨ l = [x] := by
  have h : l.length = 0 ∨ l.length = 1 := by omega
  rcases h with h0 | h1
  · exact Or.inl (List.eq_nil_of_length_eq_zero h0)
  · obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp h1
    rw [hmem a (List.mem_singleton_self a)]
    exact Or.inr rfl

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- The boundary of a relator cell has as many darts as its word has letters. -/
theorem cellDarts_length_eq_word_length (X : DiscDiagram.{u, w, v} W) (i : Fin X.rCellCount) :
    (cellDarts X i).length = (cell X i).word.length := by
  have h := congrArg List.length (X.relatorCell_word _ (cell_mem X i))
  rw [List.length_map] at h
  exact h.symm

/-- The exterior face has as many darts as the boundary word has letters. -/
theorem outerBoundary_darts_length (X : DiscDiagram.{u, w, v} W) :
    (X.faceBoundary X.outerFace).darts.length = X.boundaryWord.length := by
  rw [X.boundaryWord_length]
  exact (X.faceBoundary X.outerFace).length_eq_degree

variable {D : RelGenSet G Lambda} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **A pocket face set at `ε = 0` on monogons is not simple.**  If the source cell and the
exterior face each have one dart, then no pocket face set with sides of length `0` is simple. -/
theorem not_simple_of_monogons (K : PocketFaceSet D 0 X lo hi)
    (hsource : (cellDarts X K.source).length = 1)
    (houter : (X.faceBoundary X.outerFace).darts.length = 1) : ¬ K.Simple := by
  intro hK
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hsource
  obtain ⟨o, ho⟩ := List.length_eq_one_iff.mp houter
  have hout : outerDarts X = [X.toCombMap.alpha o] := by
    change (X.faceBoundary X.outerFace).darts.reverse.map X.toCombMap.alpha = _
    rw [ho]
    rfl
  have hsl : K.sourceArc.darts.length ≤ 1 :=
    K.sourceArc.darts_length.trans_le (K.sourceArc.length_le.trans_eq hsource)
  have htl : K.targetArc.darts.length ≤ 1 :=
    K.targetArc.darts_length.trans_le
      (K.targetArc.length_le.trans_eq ((congrArg List.length hout).trans List.length_singleton))
  have hsrc : ∀ d ∈ K.sourceArc.darts, d = x := fun d hd => by
    have h := K.sourceArc.mem_cycle_of_mem_darts hd
    rw [hx, List.mem_singleton] at h
    exact h
  have htgt : ∀ d ∈ K.targetArc.darts, d = X.toCombMap.alpha o := fun d hd => by
    have h := K.targetArc.mem_cycle_of_mem_darts hd
    rw [hout, List.mem_singleton] at h
    exact h
  have hdec := K.decomposition
  rw [List.eq_nil_of_length_eq_zero (Nat.le_zero.mp K.firstSide_length_le),
    List.eq_nil_of_length_eq_zero (Nat.le_zero.mp K.secondSide_length_le)] at hdec
  have hconn := X.toCombMap.connected_of_planar X.planar
  rcases eq_nil_or_eq_singleton hsl hsrc with ht1 | ht1 <;>
    rcases eq_nil_or_eq_singleton htl htgt with ht2 | ht2
  · have hC : K.boundary.cycle = [] := by
      rw [hdec, ht1, ht2]
      rfl
    exact K.boundary.cycle_nonempty hC
  · have hC : K.boundary.cycle = [X.toCombMap.alpha o] := by
      rw [hdec, ht1, ht2]
      rfl
    rcases eq_or_mem_of_cycle_eq_singleton hconn K.boundary (X.faceBoundary X.outerFace) ho hC
      (cell X K.source).face with h | h
    · exact (cell X K.source).face_ne_outer h
    · exact K.source_not_mem h
  · have hC : K.boundary.cycle = [X.toCombMap.alpha x] := by
      rw [hdec, ht1, ht2]
      rfl
    rcases eq_or_mem_of_cycle_eq_singleton hconn K.boundary
      (X.faceBoundary (cell X K.source).face) hx hC X.outerFace with h | h
    · exact (cell X K.source).face_ne_outer h.symm
    · exact K.outerFace_not_mem h
  · have hC : K.boundary.cycle = [X.toCombMap.alpha x, X.toCombMap.alpha o] := by
      rw [hdec, ht1, ht2]
      rfl
    have h : IsSimpleClosedWalk X.toCombMap K.boundary.cycle := hK
    rw [hC] at h
    have hchain := List.isChain_pair.mp h.chain
    rw [X.toCombMap.alpha_involutive x] at hchain
    have hfx : X.toCombMap.sigma (X.toCombMap.alpha x) = x :=
      facePerm_eq_self_of_darts_eq (X.faceBoundary (cell X K.source).face) hx
    have hvx : X.toCombMap.vertexOf (X.toCombMap.alpha x) = X.toCombMap.vertexOf x :=
      (X.toCombMap.vertexOf_sigma (X.toCombMap.alpha x)).symm.trans
        (congrArg X.toCombMap.vertexOf hfx)
    have hnd := h.vertex_nodup
    change [X.toCombMap.vertexOf (X.toCombMap.alpha x),
      X.toCombMap.vertexOf (X.toCombMap.alpha o)].Nodup at hnd
    exact (List.nodup_cons.mp hnd).1 (List.mem_singleton.mpr (hvx.trans hchain))

/-- **No O-equivalent copy of a diagram on monogons has a simple pocket face set at `ε = 0`.**  An
O-equivalence keeps the lengths of the relator words and of the boundary word. -/
theorem no_simple_of_oEquivalent_monogons {X' : DiscDiagram.{u, w, v} W}
    (e : OEquivalentDiscDiagram X X') (hcells : ∀ i, (cell X i).word.length = 1)
    (hbdry : X.boundaryWord.length = 1) {lo' hi' : ℕ} (K' : PocketFaceSet D 0 X' lo' hi') :
    ¬ K'.Simple := by
  have h := e.cellWord_eq (e.cellIndex.symm K'.source)
  rw [Equiv.apply_symm_apply] at h
  refine not_simple_of_monogons K' ?_ ?_
  · rw [cellDarts_length_eq_word_length, h]
    exact hcells _
  · rw [outerBoundary_darts_length, e.boundaryWord_eq]
    exact hbdry

/-- **The pinch fails at `ε = 0` on monogons.** -/
theorem not_pocketPinchStatement_of_monogons (hcells : ∀ i, (cell X i).word.length = 1)
    (hbdry : X.boundaryWord.length = 1) (K : PocketFaceSet D 0 X lo hi) :
    ¬ PocketPinchStatement.{u, w, v} := by
  intro h
  obtain ⟨X', K', ⟨e⟩, hK'⟩ := h D 0 W X lo hi K
  exact no_simple_of_oEquivalent_monogons e hcells hbdry K' hK'

/-- **The pinched case of the pinch fails at `ε = 0` on monogons.** -/
theorem not_pocketPinchPinchedStatement_of_monogons (hcells : ∀ i, (cell X i).word.length = 1)
    (hbdry : X.boundaryWord.length = 1) (K : PocketFaceSet D 0 X lo hi) :
    ¬ PocketPinchPinchedStatement.{u, w, v} := fun h =>
  not_pocketPinchStatement_of_monogons hcells hbdry K (pocketPinchStatement_of_pinched h)

/-- **The labelled pinch fails at `ε = 0` on monogons**, given one pocket face set in walk order of
a diagram whose labels are letters. -/
theorem not_pocketPinchLabelledStatement_of_monogons (hcells : ∀ i, (cell X i).word.length = 1)
    (hbdry : X.boundaryWord.length = 1)
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    (K : PocketFaceSet D 0 X lo hi) (hK : K.ClosedWalk) :
    ¬ PocketPinchLabelledStatement.{u, w, v} := by
  intro h
  obtain ⟨X', K', ⟨e⟩, hK'⟩ := h D 0 W X lo hi hlabel K hK
  exact no_simple_of_oEquivalent_monogons e hcells hbdry K' hK'

/-- **One step of the pinch fails at `ε = 0` on monogons**, given one pocket face set in walk order
of a diagram whose labels are letters. -/
theorem not_pocketPinchStepStatement_of_monogons (hcells : ∀ i, (cell X i).word.length = 1)
    (hbdry : X.boundaryWord.length = 1)
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    (K : PocketFaceSet D 0 X lo hi) (hK : K.ClosedWalk) :
    ¬ PocketPinchStepStatement.{u, w, v} := fun h =>
  not_pocketPinchLabelledStatement_of_monogons hcells hbdry hlabel K hK
    (pocketPinchLabelledStatement_of_step h)

#audit_axioms eq_or_mem_of_cycle_eq_singleton
#audit_axioms not_simple_of_monogons
#audit_axioms no_simple_of_oEquivalent_monogons
#audit_axioms not_pocketPinchStatement_of_monogons
#audit_axioms not_pocketPinchPinchedStatement_of_monogons
#audit_axioms not_pocketPinchLabelledStatement_of_monogons
#audit_axioms not_pocketPinchStepStatement_of_monogons

end PocketWrap

end GroupApproximation.GGT.VanKampen
