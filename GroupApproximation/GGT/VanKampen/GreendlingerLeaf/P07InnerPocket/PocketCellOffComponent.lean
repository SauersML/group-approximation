import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketLakeAbsorption
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane `PocketCellOff`: comparing exterior pieces

Lane gl-p07-07.  Write `component M P o` for the piece of the face `o`: the faces reached from `o`
by walking around faces and crossing edges that are not on the boundary of `P`.

* `eqvGen_alpha`: an edge whose two faces are both off `P` can be crossed.
* `component_mono`: a smaller face set has a larger piece.  If `P ⊆ Q` and `o ∉ Q`, the piece of
  `o` for `Q` lies in the piece for `P`.  A walk from `o` for `Q` stays off `Q`
  (`faceOf_mem_iff_of_eqvGen`), so every edge it crosses has both faces off `Q`, hence off `P`.
* `eqvGen_of_mem_boundary_cycle`: two darts on the boundary cycle of a region `A` that misses `P`
  are joined for `P`.  One boundary step turns around a face and crosses internal edges of `A`,
  whose two faces lie in `A` and so off `P`.  Then propagate along the chain
  (`List.IsChain.induction`).
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Surgery.MapCollapse Surgery.MapCollapse.ExteriorComponent

section Map

variable {M : CombMap.{v}}

/-- **Crossing an edge whose faces are both off `P`.** -/
theorem eqvGen_alpha {P : Finset M.Face} {x : M.Dart} (hx : M.faceOf x ∉ P)
    (hαx : M.faceOf (M.alpha x) ∉ P) :
    Relation.EqvGen (CombMap.FaceClassStep M (BoundaryEdge M P)) x (M.alpha x) := by
  refine Relation.EqvGen.rel _ _ (Or.inr ⟨?_, rfl⟩)
  intro hb
  rcases hb with hb | hb
  · have hb' : M.faceOf x ∈ P ∧ M.faceOf (M.alpha x) ∉ P := hb
    exact hx hb'.1
  · have hb' : M.faceOf (M.alpha x) ∈ P ∧ M.faceOf (M.alpha (M.alpha x)) ∉ P := hb
    exact hαx hb'.1

/-- **A smaller face set has a larger piece.** -/
theorem component_mono {P Q : Finset M.Face} {o f : M.Face} (hPQ : P ⊆ Q) (ho : o ∉ Q)
    (hf : f ∈ component M Q o) : f ∈ component M P o := by
  obtain ⟨y, rfl, x₀, hx₀, hxy⟩ := mem_component_iff.mp hf
  refine mem_component_iff.mpr ⟨y, rfl, x₀, hx₀, ?_⟩
  have key : ∀ {x y : M.Dart},
      Relation.EqvGen (CombMap.FaceClassStep M (BoundaryEdge M Q)) x y → M.faceOf x ∉ Q →
        Relation.EqvGen (CombMap.FaceClassStep M (BoundaryEdge M P)) x y := by
    intro x y h
    induction h with
    | rel x₁ _ hx =>
        intro hout
        rcases hx with rfl | ⟨hoff, rfl⟩
        · exact Relation.EqvGen.rel _ _ (Or.inl rfl)
        · have hαout : M.faceOf (M.alpha x₁) ∉ Q := by
            intro hin
            have hout' : M.faceOf (M.alpha (M.alpha x₁)) ∉ Q := by
              rw [M.alpha_involutive x₁]
              exact hout
            exact hoff (show Surgery.MapCollapse.IsBoundaryDart M Q x₁ ∨
                Surgery.MapCollapse.IsBoundaryDart M Q (M.alpha x₁) from
              Or.inr (show M.faceOf (M.alpha x₁) ∈ Q ∧
                M.faceOf (M.alpha (M.alpha x₁)) ∉ Q from ⟨hin, hout'⟩))
          exact eqvGen_alpha (fun h => hout (hPQ h)) (fun h => hαout (hPQ h))
    | refl x₁ =>
        intro _
        exact Relation.EqvGen.refl x₁
    | symm _ _ h₁ ih =>
        intro hout
        exact Relation.EqvGen.symm _ _ (ih (by rwa [faceOf_mem_iff_of_eqvGen h₁]))
    | trans _ _ _ h₁ _ ih₁ ih₂ =>
        intro hout
        exact Relation.EqvGen.trans _ _ _ (ih₁ hout)
          (ih₂ (by rwa [← faceOf_mem_iff_of_eqvGen h₁]))
  exact key hxy (by rw [hx₀]; exact ho)

end Map

section Diagram

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {X : DiscDiagram.{u, w, v} W}

/-- **One boundary step of a region missing `P` is joined for `P`.** -/
theorem eqvGen_of_boundaryStep {A P : Finset X.toCombMap.Face} (hAP : ∀ f ∈ A, f ∉ P)
    {d e : X.toCombMap.Dart} (h : Embedded.BoundaryStep X A d e) :
    Relation.EqvGen (CombMap.FaceClassStep X.toCombMap (BoundaryEdge X.toCombMap P)) d e := by
  obtain ⟨-, -, hr⟩ := h
  refine Relation.EqvGen.trans _ (X.toCombMap.facePerm d) _
    (Relation.EqvGen.rel _ _ (Or.inl rfl)) ?_
  induction hr with
  | refl => exact Relation.EqvGen.refl _
  | tail _ hbc ih =>
      obtain ⟨hb, hαb, rfl⟩ := hbc
      exact Relation.EqvGen.trans _ _ _ ih
        (Relation.EqvGen.trans _ _ _ (eqvGen_alpha (hAP _ hb) (hAP _ hαb))
          (Relation.EqvGen.rel _ _ (Or.inl rfl)))

/-- **Two darts on the boundary cycle of a region missing `P` are joined for `P`.** -/
theorem eqvGen_of_mem_boundary_cycle {A P : Finset X.toCombMap.Face}
    (B : Embedded.FaceSetBoundary X A) (hAP : ∀ f ∈ A, f ∉ P) {x y : X.toCombMap.Dart}
    (hx : x ∈ B.cycle) (hy : y ∈ B.cycle) :
    Relation.EqvGen (CombMap.FaceClassStep X.toCombMap (BoundaryEdge X.toCombMap P)) x y := by
  have hall : ∀ z ∈ B.cycle,
      Relation.EqvGen (CombMap.FaceClassStep X.toCombMap (BoundaryEdge X.toCombMap P))
        (B.cycle.head B.cycle_nonempty) z := by
    refine List.IsChain.induction (fun z =>
      Relation.EqvGen (CombMap.FaceClassStep X.toCombMap (BoundaryEdge X.toCombMap P))
        (B.cycle.head B.cycle_nonempty) z) B.cycle B.cycle_chain ?_ ?_
    · intro _ _ hst hp
      exact Relation.EqvGen.trans _ _ _ hp (eqvGen_of_boundaryStep hAP hst)
    · intro _
      exact Relation.EqvGen.refl _
  exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (hall x hx)) (hall y hy)

end Diagram

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.eqvGen_alpha
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.component_mono
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.eqvGen_of_boundaryStep
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.eqvGen_of_mem_boundary_cycle
