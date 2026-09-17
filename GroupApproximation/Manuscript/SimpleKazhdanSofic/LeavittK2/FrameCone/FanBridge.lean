import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameCone.Endpoint
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameFan.FrameComplex
import GroupApproximation.Meta.AxiomGuard

/-!
# Frame cone: the fan interface of lane `sk-leavitt-10`

Khanh (arXiv:2609.08428), Prop. `prop:frame-cone`, as used in the fan argument (tex l.539):

> Let `E` be a finite set of frames of lengths `k_i ≤ r-2` in `L^r`. Then there is `v ∈ L^r`
> such that `(v, f_i)` is a frame for every `i ∈ E`.

`FrameFan.BinaryLeavittFrameConeFourStatement` asks for a cone vertex over finitely many
vertices (1-frames) and edges (2-frames) of `X_4(L)`. Apply the list cone
`frame_cone_four_list_of_wordMultiplier` to `[] :: ([w] for w ∈ vs) ++ ([u,w] for (u,w) ∈ es)`:
the empty frame makes `v` a vertex, and `IsFrame [v,w]`, `IsFrame [v,u,w]` are exactly
`IsFrameEdge`, `IsFrameTriangle` (first columns of an invertible matrix).
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameCone

open GroupApproximation

section Generic

variable {A : Type*} [Ring A]

theorem isFrame_nil : IsFrame ([] : List (Fin 4 → A)) :=
  ⟨Nat.zero_le _, 1, fun _ hj _ => absurd hj (Nat.not_lt_zero _)⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameCone.isFrame_nil

theorem isFrame_single {u : Fin 4 → A} (hu : FrameFan.IsFrameVertex A u) : IsFrame [u] := by
  obtain ⟨g, hg⟩ := hu
  refine ⟨by simp, g, fun j hj i => ?_⟩
  rcases j with ⟨_ | m, hjv⟩
  · exact hg i
  · exact absurd (Nat.lt_of_succ_lt_succ hj) (Nat.not_lt_zero m)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameCone.isFrame_single

theorem isFrame_pair {u w : Fin 4 → A} (huw : FrameFan.IsFrameEdge A u w) : IsFrame [u, w] := by
  obtain ⟨g, hg⟩ := huw
  refine ⟨by simp, g, fun j hj i => ?_⟩
  rcases j with ⟨_ | _ | m, hjv⟩
  · exact (hg i).1
  · exact (hg i).2
  · exact absurd (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hj)) (Nat.not_lt_zero m)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameCone.isFrame_pair

theorem vertex_of_isFrame {v : Fin 4 → A} (h : IsFrame [v]) : FrameFan.IsFrameVertex A v := by
  obtain ⟨-, g, hg⟩ := h
  exact ⟨g, fun r => hg 0 (by decide) r⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameCone.vertex_of_isFrame

theorem edge_of_isFrame {v w : Fin 4 → A} (h : IsFrame [v, w]) : FrameFan.IsFrameEdge A v w := by
  obtain ⟨-, g, hg⟩ := h
  exact ⟨g, fun r => ⟨hg 0 (by decide) r, hg 1 (by decide) r⟩⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameCone.edge_of_isFrame

theorem triangle_of_isFrame {v u w : Fin 4 → A} (h : IsFrame [v, u, w]) :
    FrameFan.IsFrameTriangle A v u w := by
  obtain ⟨-, g, hg⟩ := h
  exact ⟨g, fun r => ⟨hg 0 (by decide) r, hg 1 (by decide) r, hg 2 (by decide) r⟩⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameCone.triangle_of_isFrame

end Generic

/-- **Lane `sk-leavitt-10` interface.** The rank-four frame cone over `L = L_{F_2}(1,2)` in the
vertex/edge form of `FrameFan.BinaryLeavittFrameConeFourStatement`, reduced to the word
multiplier (Khanh Lemma 4.1, lane 08). -/
theorem binaryLeavittFrameConeFour_of_wordMultiplier (h : WordMultiplierStatement) :
    FrameFan.BinaryLeavittFrameConeFourStatement := by
  unfold FrameFan.BinaryLeavittFrameConeFourStatement FrameFan.FrameConeFourStatement
  intro vs es hes
  have hF : ∀ f ∈ ([] :: ((vs.map fun w => [w.1]) ++ es.map fun x => [x.1.1, x.2.1])),
      f.length ≤ 2 ∧ IsFrame f := by
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact ⟨by simp, isFrame_nil⟩
    rcases List.mem_append.mp hf with hf | hf
    · obtain ⟨w, -, rfl⟩ := List.mem_map.mp hf
      exact ⟨by simp, isFrame_single w.2⟩
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hf
      exact ⟨by simp, isFrame_pair (hes x hx)⟩
  obtain ⟨v, hv⟩ := frame_cone_four_list_of_wordMultiplier h _ hF
  refine ⟨⟨v, vertex_of_isFrame (hv [] List.mem_cons_self)⟩, fun w hw => ?_, fun x hx => ?_⟩
  · exact edge_of_isFrame (hv [w.1]
      (List.mem_cons_of_mem _ (List.mem_append_left _
        (List.mem_map_of_mem (f := fun w : FrameFan.FrameVertex
          (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) => [w.1]) hw))))
  · exact triangle_of_isFrame (hv [x.1.1, x.2.1]
      (List.mem_cons_of_mem _ (List.mem_append_right _
        (List.mem_map_of_mem (f := fun x : FrameFan.FrameVertex
          (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) ×
            FrameFan.FrameVertex (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) =>
              [x.1.1, x.2.1]) hx))))

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameCone.binaryLeavittFrameConeFour_of_wordMultiplier

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameCone
