import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVLowKZeroCore.Filtration
import GroupApproximation.Leavitt.LeavittSimplicity

/-!
# Clearing the deletion letters of an element of `L_k(1,2)`

Ingredient of `binaryLeavitt_idempotent_dichotomy` (manuscript
`simple_kazhdan_sofic_group.tex`, l.733-735, `sec:questions`, question Q2).

Every `x ∈ L_k(1,2)` is a finite combination of monomials `s_α t_β`.  So
there are bounds `m, N` such that, for every word `δ` of length `≥ m`, the
product `x · s_δ` is a combination of `s`-words of length `< N + |δ|`.

For an element `e` and a length `m`, set `qvec k e m δ = e · s_δ`, indexed by
the binary words `δ` of length `m`.  Then `e = ∑_δ qvec δ · t_δ`, so
`x · qvec = 0` forces `x · e = 0`.
-/

namespace GroupApproximation.Full.LVLowKZeroCore

open GroupApproximation.BinaryLeavitt

noncomputable section

variable (k : Type) [Field k]

/-- Right multiplication by long `s`-words clears the deletion letters. -/
theorem exists_clearing (x : BinaryLeavittAlgebra k) :
    ∃ m N : ℕ, ∀ δ : List (Fin 2), m ≤ δ.length →
      x * (family k).wordS δ ∈ fil k (N + δ.length) := by
  have hx : x ∈ Submodule.span k (monomialSet k) := by
    rw [span_monomialSet_eq_top k]
    exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem u hu =>
      obtain ⟨a, b, rfl⟩ := hu
      refine ⟨b.length, a.length + 1, fun δ hδ => ?_⟩
      rw [mul_assoc]
      by_cases hbδ : b <+: δ
      · obtain ⟨δ₂, rfl⟩ := hbδ
        rw [LeavittFamily.wordT_mul_wordS_append_left, ← LeavittFamily.wordS_append]
        refine wordS_mem_fil k ?_
        rw [List.length_append, List.length_append]
        omega
      · have hδb : ¬δ <+: b := by
          intro h
          obtain rfl := h.eq_of_length (le_antisymm h.length_le hδ)
          exact hbδ (List.prefix_refl _)
        rw [LeavittFamily.wordT_mul_wordS_of_incomparable _ _ hbδ hδb, mul_zero]
        exact Submodule.zero_mem _
  | zero =>
      refine ⟨0, 0, fun δ _ => ?_⟩
      rw [zero_mul]
      exact Submodule.zero_mem _
  | add v w _ _ hv hw =>
      obtain ⟨m₁, N₁, h₁⟩ := hv
      obtain ⟨m₂, N₂, h₂⟩ := hw
      refine ⟨max m₁ m₂, max N₁ N₂, fun δ hδ => ?_⟩
      rw [add_mul]
      exact Submodule.add_mem _
        (fil_mono k (by omega) (h₁ δ (by omega)))
        (fil_mono k (by omega) (h₂ δ (by omega)))
  | smul c v _ hv =>
      obtain ⟨m, N, h⟩ := hv
      refine ⟨m, N, fun δ hδ => ?_⟩
      rw [smul_mul_assoc]
      exact Submodule.smul_mem _ c (h δ hδ)

/-- The column `δ ↦ e · s_δ` over binary words of length `m`. -/
def qvec (e : BinaryLeavittAlgebra k) (m : ℕ) (δ : Fin m → Fin 2) : BinaryLeavittAlgebra k :=
  e * (family k).wordS (List.ofFn δ)

theorem qvec_apply (e : BinaryLeavittAlgebra k) (m : ℕ) (δ : Fin m → Fin 2) :
    qvec k e m δ = e * (family k).wordS (List.ofFn δ) := rfl

theorem eq_sum_qvec (e : BinaryLeavittAlgebra k) (m : ℕ) :
    e = ∑ δ : Fin m → Fin 2, qvec k e m δ * (family k).wordT (List.ofFn δ) :=
  (family k).eq_sum_mul_wordS_mul_wordT e m

theorem mul_eq_zero_of_mul_qvec_eq_zero {e x : BinaryLeavittAlgebra k} {m : ℕ}
    (h : ∀ δ : Fin m → Fin 2, x * qvec k e m δ = 0) : x * e = 0 := by
  rw [eq_sum_qvec k e m, Finset.mul_sum]
  refine Finset.sum_eq_zero fun δ _ => ?_
  rw [← mul_assoc, h δ, zero_mul]

theorem mul_qvec_of_idempotent {e : BinaryLeavittAlgebra k} (he : IsIdempotentElem e) (m : ℕ)
    (δ : Fin m → Fin 2) : e * qvec k e m δ = qvec k e m δ := by
  rw [qvec_apply, ← mul_assoc, he.eq]

/-- With clearing bounds `(m, N)` for `e`, every entry of the column lies in
`fil k (N + m)`. -/
theorem qvec_mem_fil {e : BinaryLeavittAlgebra k} {m N : ℕ}
    (h : ∀ δ : List (Fin 2), m ≤ δ.length → e * (family k).wordS δ ∈ fil k (N + δ.length))
    (δ : Fin m → Fin 2) : qvec k e m δ ∈ fil k (N + m) := by
  have hδ := h (List.ofFn δ) (by rw [List.length_ofFn])
  rw [List.length_ofFn] at hδ
  exact hδ

end

end GroupApproximation.Full.LVLowKZeroCore
