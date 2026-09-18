import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVFrame.Endpoint
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVFrame.FrameFour
import GroupApproximation.Meta.AxiomGuard

/-!
# The frame complex `X₄(L)` is simply connected (leaf T1c)

`simple_kazhdan_sofic_group.tex`, `sec:questions`, l.733-735 (leaf T1c of the `K₂(4, L) = ⊥` tree),
with `L = L_{F_2}(1,2)`.

Khanh (arXiv:2609.08428), Prop. `prop:frame-cone` (tex l.360), in the form the fan argument
(tex l.539) needs: "any finite collection of vertices and edges has a common apex".

* `isFrame_nil/single/pair`, `vertex_of_isFrame`, `edge_of_isFrame`, `triangle_of_isFrame`:
  the list predicate `IsFrame` and `IsFrameVertex/Edge/Triangle` are the same "first columns of
  an invertible matrix" condition.
* `hasFanApex_frameComplexFour`: apply the list cone `frame_cone_four_list` to
  `[] :: ([w] for w ∈ vs) ++ ([u,w] for (u,w) ∈ es)`. The empty frame makes the apex a vertex.
* `frameComplexFour_simplyConnected`: leaf T1c, from `simplyConnected_of_hasFanApex`.

Lane LVFrame: port of the foreign module `LeavittK2/FrameCone/FanBridge.lean`, stated for the
lane's `frameComplexFour` (same fields as `LeavittK2.FrameFan.frameComplexFour`).
-/

namespace GroupApproximation.Full.LVFrame

section Generic

variable {A : Type*} [Ring A]

theorem isFrame_nil : IsFrame ([] : List (Fin 4 → A)) :=
  ⟨Nat.zero_le _, 1, fun _ hj _ => absurd hj (Nat.not_lt_zero _)⟩

#audit_axioms GroupApproximation.Full.LVFrame.isFrame_nil

theorem isFrame_single {u : Fin 4 → A} (hu : IsFrameVertex A u) : IsFrame [u] := by
  obtain ⟨g, hg⟩ := hu
  refine ⟨by simp, g, fun j hj i => ?_⟩
  rcases j with ⟨_ | m, hjv⟩
  · exact hg i
  · exact absurd (Nat.lt_of_succ_lt_succ hj) (Nat.not_lt_zero m)

#audit_axioms GroupApproximation.Full.LVFrame.isFrame_single

theorem isFrame_pair {u w : Fin 4 → A} (huw : IsFrameEdge A u w) : IsFrame [u, w] := by
  obtain ⟨g, hg⟩ := huw
  refine ⟨by simp, g, fun j hj i => ?_⟩
  rcases j with ⟨_ | _ | m, hjv⟩
  · exact (hg i).1
  · exact (hg i).2
  · exact absurd (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hj)) (Nat.not_lt_zero m)

#audit_axioms GroupApproximation.Full.LVFrame.isFrame_pair

theorem vertex_of_isFrame {v : Fin 4 → A} (h : IsFrame [v]) : IsFrameVertex A v := by
  obtain ⟨-, g, hg⟩ := h
  exact ⟨g, fun r => hg 0 (by decide) r⟩

#audit_axioms GroupApproximation.Full.LVFrame.vertex_of_isFrame

theorem edge_of_isFrame {v w : Fin 4 → A} (h : IsFrame [v, w]) : IsFrameEdge A v w := by
  obtain ⟨-, g, hg⟩ := h
  exact ⟨g, fun r => ⟨hg 0 (by decide) r, hg 1 (by decide) r⟩⟩

#audit_axioms GroupApproximation.Full.LVFrame.edge_of_isFrame

theorem triangle_of_isFrame {v u w : Fin 4 → A} (h : IsFrame [v, u, w]) :
    IsFrameTriangle A v u w := by
  obtain ⟨-, g, hg⟩ := h
  exact ⟨g, fun r => ⟨hg 0 (by decide) r, hg 1 (by decide) r, hg 2 (by decide) r⟩⟩

#audit_axioms GroupApproximation.Full.LVFrame.triangle_of_isFrame

end Generic

/-- **Cone property of `X₄(L)`** (Khanh Prop. 4.2, tex l.360, as used at tex l.539): every finite
list of vertices and ordered edges of `X₄(L)` has a common apex. -/
theorem hasFanApex_frameComplexFour :
    HasFanApex (frameComplexFour (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))) := by
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
      have hx' : IsFrameEdge (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) x.1.1 x.2.1 := hes x hx
      exact ⟨by simp, isFrame_pair hx'⟩
  obtain ⟨v, hv⟩ := frame_cone_four_list _ hF
  refine ⟨⟨v, vertex_of_isFrame (hv [] (List.mem_cons.2 (Or.inl rfl)))⟩, fun w hw => ?_,
    fun x hx => ?_⟩
  · exact edge_of_isFrame (hv [w.1]
      (List.mem_cons_of_mem _ (List.mem_append_left _
        (List.mem_map_of_mem (f := fun w : FrameVertex
          (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) => [w.1]) hw))))
  · exact triangle_of_isFrame (hv [x.1.1, x.2.1]
      (List.mem_cons_of_mem _ (List.mem_append_right _
        (List.mem_map_of_mem (f := fun x : FrameVertex
          (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) ×
            FrameVertex (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) =>
              [x.1.1, x.2.1]) hx))))

#audit_axioms GroupApproximation.Full.LVFrame.hasFanApex_frameComplexFour

/-- **Leaf T1c** (`simple_kazhdan_sofic_group.tex` l.733-735; Khanh tex l.539): the ordered frame
complex `X₄(L)`, `L = L_{F_2}(1,2)`, is combinatorially simply connected. It is connected, and
every edge loop is `Homotopic` (`EqvGen` of backtrack and triangle moves) to the constant path. -/
theorem frameComplexFour_simplyConnected :
    (frameComplexFour (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))).SimplyConnected :=
  simplyConnected_of_hasFanApex hasFanApex_frameComplexFour

#audit_axioms GroupApproximation.Full.LVFrame.frameComplexFour_simplyConnected

end GroupApproximation.Full.LVFrame
