import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.Frame.StabBlock
import GroupApproximation.Meta.AxiomGuard

/-!
# Block form of the edge stabilizer `K = {k(a, b, H)}`

Lane `sk-leavitt-07` (carto `sk-leavitt`).  Khanh (arXiv:2609.08428v1), proof of Theorem 5.1:
the stabilizer of the base edge `(v_0, v_1)` consists of the matrices `k(a, b, H)`.  With the
last-index convention (`v_0 = e_last`, `v_1 = e_{cs last}` in `A^{m+2}`):

`k(a, b, H) = frameJMat a (frameJMat b H) = [[H, 0, 0], [b, 1, 0], [a', 0, 1]]`,

with `H ∈ GL_m(A)`, `b : A^m`, and last row `a : A^{m+1}` with `a last = 0`.

* `frameEdgeStab_eq`: `g ∈ K ↔ ∃ H a b, a last = 0 ∧ g = frameJMat a (frameJMat b H)`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

variable {A : Type*} [Ring A] {m : ℕ}

/-- `K = {k(a, b, H)}`. -/
theorem frameEdgeStab_eq (g : (Matrix (Fin (m + 1 + 1)) (Fin (m + 1 + 1)) A)ˣ) :
    g ∈ frameEdgeStab A m ↔ ∃ H : (Matrix (Fin m) (Fin m) A)ˣ, ∃ a : Fin (m + 1) → A,
      ∃ b : Fin m → A, a (Fin.last m) = 0 ∧
        (g : Matrix (Fin (m + 1 + 1)) (Fin (m + 1 + 1)) A) = frameJMat a (frameJMat b H) := by
  constructor
  · intro hg
    have hcs := (smul_single_eq_self_iff g (Fin.castSucc (Fin.last m))).1
      ((mem_frameEdgeStab_iff.1 hg).2)
    obtain ⟨H1, a, hga⟩ := (frameVertexStab_eq g).1 (frameEdgeStab_le_frameVertexStab hg)
    have hH1 : H1 ∈ frameVertexStab A m := by
      rw [mem_frameVertexStab_iff, smul_single_eq_self_iff]
      intro i
      have h := hcs (Fin.castSucc i)
      rw [hga, frameJMat_castSucc_castSucc] at h
      rw [h]
      rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
      · rw [Pi.single_eq_of_ne ((Fin.castSucc_injective _).ne (Fin.castSucc_ne_last i)),
          Pi.single_eq_of_ne (Fin.castSucc_ne_last i)]
      · rw [Pi.single_eq_same, Pi.single_eq_same]
    have ha : a (Fin.last m) = 0 := by
      have h := hcs (Fin.last (m + 1))
      rw [hga, frameJMat_last_castSucc, Pi.single_eq_of_ne (Fin.castSucc_ne_last _).symm] at h
      exact h
    obtain ⟨H, b, hH⟩ := (frameVertexStab_eq H1).1 hH1
    exact ⟨H, a, b, ha, by rw [hga, hH]⟩
  · rintro ⟨H, a, b, ha, hg⟩
    rw [mem_frameEdgeStab_iff, smul_single_eq_self_iff, smul_single_eq_self_iff]
    refine ⟨fun i => ?_, fun i => ?_⟩
    · rw [hg]
      rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
      · rw [frameJMat_castSucc_last, Pi.single_eq_of_ne (Fin.castSucc_ne_last i)]
      · rw [frameJMat_last_last, Pi.single_eq_same]
    · rw [hg]
      rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
      · rw [frameJMat_castSucc_castSucc]
        rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
        · rw [frameJMat_castSucc_last,
            Pi.single_eq_of_ne ((Fin.castSucc_injective _).ne (Fin.castSucc_ne_last i))]
        · rw [frameJMat_last_last, Pi.single_eq_same]
      · rw [frameJMat_last_castSucc, ha, Pi.single_eq_of_ne (Fin.castSucc_ne_last _).symm]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameEdgeStab_eq

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
