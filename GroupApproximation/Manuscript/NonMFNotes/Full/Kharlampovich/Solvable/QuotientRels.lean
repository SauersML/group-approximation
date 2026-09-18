/-
Copyright (c) 2026. All rights reserved.
-/
import GroupApproximation.Manuscript.NonMFNotes.Full.Kharlampovich.Solvable.QuotientCore
import GroupApproximation.Manuscript.NonMFNotes.Full.Kharlampovich.Solvable.BRPw
import GroupApproximation.Manuscript.NonMFNotes.Full.Kharlampovich.Forward.ConfigBasic

/-!
# The relations G3 and G4 in `G(M)`

Input for `thm:fixed-radical-membership` of `non_mf_group_notes.tex`
(Kharlampovich--Myasnikov--Sapir, arXiv:1204.6506, Sec. 4, Lemma `lH`, `p = 2`).

In `G(M)`, with `α = a_{n+1}`, `α' = a'_{n+1}` and `A = A_{n+1}`, the relators G3 give
`α' A α'⁻¹ = α A α⁻¹ A⁻¹` and `[A, A^α] = 1`, the hypotheses of Lemma `lBRG`
(`BR.conj_commute`).  The relators G4 give the same shape for `ã_{n+1}, ã'_{n+1}` and `A_0`,
together with `[A_0^{t}, A_0] = 1` for every `t = ã_1^{ε_1} ⋯ ã_K^{ε_K}` with
`ε_i ∈ {-1, 0, 1}` (`g4_base`), the base case of the multi-variable Lemma `lBRG`.
-/

namespace GroupApproximation.Full.Kharlampovich
namespace KMS
namespace QS

open Forward

variable {K N : ℕ} (M : Minsky.Machine K N)

/-! ## Membership of the relators -/

theorem g3_conj_mem (n : Fin K) :
    khConj (gA (N := N) n.succ) (ga n)⁻¹ * (gA n.succ)⁻¹ * (khConj (gA n.succ) (ga' n)⁻¹)⁻¹
      ∈ relators M := by
  unfold relators
  refine Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _
    (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _
      (Set.mem_union_right _ ?_)))))))
  unfold g3Relators
  refine Set.mem_union_left _ (Set.mem_union_left _ ?_)
  exact ⟨n, rfl⟩

theorem g3_comm_mem (n : Fin K) :
    khComm (khConj (gA (N := N) n.succ) (ga n)) (gA n.succ) ∈ relators M := by
  unfold relators
  refine Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _
    (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _
      (Set.mem_union_right _ ?_)))))))
  unfold g3Relators
  refine Set.mem_union_left _ (Set.mem_union_right _ ?_)
  exact ⟨n, rfl⟩

theorem g4_conj_mem (n : Fin K) :
    khConj (gA (K := K) (N := N) 0) (gta n)⁻¹ * (gA 0)⁻¹ * (khConj (gA 0) (gta' n)⁻¹)⁻¹
      ∈ relators M := by
  unfold relators
  refine Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _
    (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _
      (Set.mem_union_right _ ?_))))))
  unfold g4Relators
  refine Set.mem_union_left _ ?_
  exact ⟨n, rfl⟩

theorem g4_comm_mem (α : Fin K → Fin 3) :
    khComm (khConj (gA (K := K) (N := N) 0) (zword gta α)) (gA 0) ∈ relators M := by
  unfold relators
  refine Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _
    (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _
      (Set.mem_union_right _ ?_))))))
  unfold g4Relators
  refine Set.mem_union_right _ ?_
  exact ⟨α, rfl⟩

/-! ## The relations in `G(M)` -/

/-- G3: `a'_{n+1} A a'_{n+1}⁻¹ = a_{n+1} A a_{n+1}⁻¹ A⁻¹` for `A = A_{n+1}`. -/
theorem g3_conj (n : Fin K) :
    kLet M (.a' n) * kLet M (.bigA n.succ) * (kLet M (.a' n))⁻¹
      = kLet M (.a n) * kLet M (.bigA n.succ) * (kLet M (.a n))⁻¹
        * (kLet M (.bigA n.succ))⁻¹ := by
  have h := mk_eq_one_of_mem_relators M (g3_conj_mem M n)
  simp only [khConj, inv_inv, map_mul, map_inv] at h
  exact (mul_inv_eq_one.mp h).symm

/-- G3: `A_{n+1}` commutes with `A_{n+1}^{a_{n+1}}`. -/
theorem g3_comm (n : Fin K) :
    Commute (kLet M (.bigA n.succ))
      ((kLet M (.a n))⁻¹ * kLet M (.bigA n.succ) * kLet M (.a n)) := by
  have h := mk_eq_one_of_mem_relators M (g3_comm_mem M n)
  rw [map_khComm, map_khConj] at h
  exact (commute_of_khComm_eq_one h).symm

/-- G4: `ã'_{n+1} A_0 ã'_{n+1}⁻¹ = ã_{n+1} A_0 ã_{n+1}⁻¹ A_0⁻¹`. -/
theorem g4_conj (n : Fin K) :
    kLet M (.ta' n) * kLet M (.bigA 0) * (kLet M (.ta' n))⁻¹
      = kLet M (.ta n) * kLet M (.bigA 0) * (kLet M (.ta n))⁻¹ * (kLet M (.bigA 0))⁻¹ := by
  have h := mk_eq_one_of_mem_relators M (g4_conj_mem M n)
  simp only [khConj, inv_inv, map_mul, map_inv] at h
  exact (mul_inv_eq_one.mp h).symm

/-- G4: `A_0` commutes with `A_0^{t}` for `t = ã_1^{α_1 - 1} ⋯ ã_K^{α_K - 1}`. -/
theorem g4_comm (α : Fin K → Fin 3) :
    Commute (kLet M (.bigA 0))
      ((PresentedGroup.mk (relators M) (zword gta α))⁻¹ * kLet M (.bigA 0) *
        PresentedGroup.mk (relators M) (zword gta α)) := by
  have h := mk_eq_one_of_mem_relators M (g4_comm_mem M α)
  rw [map_khComm, map_khConj] at h
  exact (commute_of_khComm_eq_one h).symm

/-- The image of `zword gta α` is the product `∏ ã_n^{α_n - 1}` in the form `BR.pw`. -/
theorem mk_zword_eq (α : Fin K → Fin 3) (β : Fin K → ℤ)
    (hβ : ∀ n, ((α n).val : ℤ) - 1 = β n) :
    PresentedGroup.mk (relators M) (zword gta α)
      = BR.pw (fun n => kLet M (.ta n)) (fun n => kLet M (.ta' n)) β 0 := by
  have h := map_foldl_zpow (PresentedGroup.mk (relators M)) (gta (N := N))
    (fun n => ((α n).val : ℤ) - 1) (List.finRange K) 1
  simp only [map_one] at h
  refine h.trans ?_
  show BR.lprod (fun n => kLet M (.ta n) ^ (((α n).val : ℤ) - 1)) (List.finRange K)
    = BR.lprod (BR.fac (fun n => kLet M (.ta n)) (fun n => kLet M (.ta' n)) β 0)
      (List.finRange K)
  refine BR.lprod_congr (fun n => ?_) _
  show kLet M (.ta n) ^ (((α n).val : ℤ) - 1)
    = kLet M (.ta n) ^ β n * kLet M (.ta' n) ^ (0 : ℤ)
  rw [zpow_zero, mul_one, hβ n]

/-- The base case of the multi-variable Lemma `lBRG` for `A_0`: for exponents
`β_n ∈ {-1, 0, 1}`, `A_0^{t}` commutes with `A_0`, where `t = ∏ ã_n^{β_n}` (G4). -/
theorem g4_base (β : Fin K → ℤ) (hβ : ∀ n, -1 ≤ β n ∧ β n ≤ 1) :
    Commute ((BR.pw (fun n => kLet M (.ta n)) (fun n => kLet M (.ta' n)) β 0)⁻¹ *
        kLet M (.bigA 0) * BR.pw (fun n => kLet M (.ta n)) (fun n => kLet M (.ta' n)) β 0)
      (kLet M (.bigA 0)) := by
  obtain ⟨α, hα⟩ : ∃ α : Fin K → Fin 3, ∀ n, ((α n).val : ℤ) - 1 = β n := by
    refine ⟨fun n => ⟨(β n + 1).toNat, ?_⟩, fun n => ?_⟩
    · obtain ⟨h1, h2⟩ := hβ n
      have h3 := Int.toNat_of_nonneg (show 0 ≤ β n + 1 by omega)
      omega
    · obtain ⟨h1, _⟩ := hβ n
      have h3 := Int.toNat_of_nonneg (show 0 ≤ β n + 1 by omega)
      show (((β n + 1).toNat : ℕ) : ℤ) - 1 = β n
      omega
  rw [← mk_zword_eq M α β hα]
  exact (g4_comm M α).symm

/-- The letters `ã_n, ã'_n` pairwise commute (G1). -/
theorem commute_t (n m : Fin K) :
    Commute (kLet M (.ta n)) (kLet M (.ta m)) ∧ Commute (kLet M (.ta n)) (kLet M (.ta' m)) ∧
      Commute (kLet M (.ta' n)) (kLet M (.ta' m)) :=
  ⟨commute_kLet_of_mem M (small_mem_relators M (s := .ta n) (t := .ta m) trivial trivial),
    commute_kLet_of_mem M (small_mem_relators M (s := .ta n) (t := .ta' m) trivial trivial),
    commute_kLet_of_mem M (small_mem_relators M (s := .ta' n) (t := .ta' m) trivial trivial)⟩

end QS
end KMS
end GroupApproximation.Full.Kharlampovich
