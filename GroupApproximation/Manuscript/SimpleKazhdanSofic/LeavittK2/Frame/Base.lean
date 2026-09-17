import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.Frame.Swap
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.Frame.VertexComplex
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownInjective.Setting
import GroupApproximation.Meta.AxiomGuard

/-!
# The base simplices of `X_{m+3}(A)` and Brown's setting

Lane `sk-leavitt-07` (carto `sk-leavitt`).  Last-index convention: `v_0 = e_last`,
`v_1 = e_{cs last}` and `h v_1 = e_{cs cs last}`.

* `frameTri_base`: `(e_last, e_{cs last}, e_{cs cs last})` is an ordered 3-frame.
* `frameV0`, `frameV1`, `frameComplex_edge_base`, `frameComplex_tri_base`.
* `frame_edge_transitive_base`, `frame_tri_transitive_base`: transitivity in Brown's form.
* `frameBrownSetting A m`: lane 12's `BrownSetting` for `GL_{m+3}(A)` acting on `X_{m+3}(A)`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

variable {A : Type*} [Ring A] {m : ℕ}

/-- The index embedding `0 ↦ last`, `1 ↦ cs last`, `2 ↦ cs cs last` (value `m + (2 - i)`). -/
def frameTriIdx (m : ℕ) : Fin 3 ↪ Fin (m + 1 + 1 + 1) where
  toFun i := ⟨m + (2 - i.val), by omega⟩
  inj' i j hij := by
    have h : m + (2 - i.val) = m + (2 - j.val) := Fin.mk.inj hij
    have hi := i.isLt
    have hj := j.isLt
    exact Fin.ext (by omega)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameTriIdx

/-- The base ordered triangle `(e_last, e_{cs last}, e_{cs cs last})`. -/
theorem frameTri_base :
    frameTri (Pi.single (Fin.last (m + 1 + 1)) 1 : Fin (m + 1 + 1 + 1) → A)
      (Pi.single (Fin.castSucc (Fin.last (m + 1))) 1)
      (Pi.single (Fin.castSucc (Fin.castSucc (Fin.last m))) 1) :=
  ⟨1, frameTriIdx m, fun i => by fin_cases i <;> exact (one_smul _ _).symm⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameTri_base

/-- The base vertex `v_0 = e_last`. -/
def frameV0 (A : Type*) [Ring A] (m : ℕ) : FrameVertices A (m + 1 + 1 + 1) :=
  ⟨Pi.single (Fin.last (m + 1 + 1)) 1, (frameTri_base (A := A) (m := m)).edge01.vertex0⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameV0

/-- The second base vertex `v_1 = e_{cs last}`. -/
def frameV1 (A : Type*) [Ring A] (m : ℕ) : FrameVertices A (m + 1 + 1 + 1) :=
  ⟨Pi.single (Fin.castSucc (Fin.last (m + 1))) 1,
    (frameTri_base (A := A) (m := m)).edge01.vertex1⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameV1

theorem frameComplex_edge_base :
    (frameComplex A (m + 1 + 1 + 1)).edge (frameV0 A m) (frameV1 A m) :=
  (frameTri_base (A := A) (m := m)).edge01

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameComplex_edge_base

theorem frameTau_smul_frameV0 : frameTau A (m + 1) • frameV0 A m = frameV1 A m :=
  Subtype.ext frameTau_smul_last

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameTau_smul_frameV0

theorem frameTau_smul_frameV1 : frameTau A (m + 1) • frameV1 A m = frameV0 A m :=
  Subtype.ext frameTau_smul_castSucc

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameTau_smul_frameV1

theorem frameHSwap_smul_frameV0 : frameHSwap A m • frameV0 A m = frameV0 A m :=
  Subtype.ext frameHSwap_smul_last

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameHSwap_smul_frameV0

theorem frameComplex_tri_base :
    (frameComplex A (m + 1 + 1 + 1)).tri (frameV0 A m) (frameV1 A m)
      (frameHSwap A m • frameV1 A m) := by
  show frameTri (Pi.single (Fin.last (m + 1 + 1)) 1 : Fin (m + 1 + 1 + 1) → A)
    (Pi.single (Fin.castSucc (Fin.last (m + 1))) 1)
    (frameHSwap A m • (Pi.single (Fin.castSucc (Fin.last (m + 1))) 1 : Fin (m + 1 + 1 + 1) → A))
  rw [frameHSwap_smul_castSucc]
  exact frameTri_base

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameComplex_tri_base

theorem frame_edge_transitive_base (a b : FrameVertices A (m + 1 + 1 + 1))
    (hab : (frameComplex A (m + 1 + 1 + 1)).edge a b) :
    ∃ g : (Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) A)ˣ,
      g • frameV0 A m = a ∧ g • frameV1 A m = b :=
  frame_transitive_edge frameComplex_edge_base hab

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frame_edge_transitive_base

theorem frame_tri_transitive_base (a b c : FrameVertices A (m + 1 + 1 + 1))
    (habc : (frameComplex A (m + 1 + 1 + 1)).tri a b c) :
    ∃ g : (Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) A)ˣ,
      g • frameV0 A m = a ∧ g • frameV1 A m = b ∧ g • (frameHSwap A m • frameV1 A m) = c :=
  frame_transitive_tri frameComplex_tri_base habc

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frame_tri_transitive_base

/-- Lane 12's Brown setting for `GL_{m+3}(A)` acting on the frame complex `X_{m+3}(A)`. -/
def frameBrownSetting (A : Type*) [Ring A] (m : ℕ) :
    BrownInjective.BrownSetting (Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) A)ˣ
      (FrameVertices A (m + 1 + 1 + 1)) where
  edge := (frameComplex A (m + 1 + 1 + 1)).edge
  tri := (frameComplex A (m + 1 + 1 + 1)).tri
  edge_smul := fun g _ _ h => frameEdge.smul h g
  tri_edge := fun _ _ _ h => frameTri.edge02 h
  v0 := frameV0 A m
  v1 := frameV1 A m
  edge_base := frameComplex_edge_base
  edge_transitive := frame_edge_transitive_base
  tau := frameTau A (m + 1)
  tau_v0 := frameTau_smul_frameV0
  tau_v1 := frameTau_smul_frameV1
  h := frameHSwap A m
  h_v0 := frameHSwap_smul_frameV0
  h_mul_h := frameHSwap_mul_self
  braid := frameTau_frameHSwap_braid
  tri_transitive := frame_tri_transitive_base

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameBrownSetting

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
