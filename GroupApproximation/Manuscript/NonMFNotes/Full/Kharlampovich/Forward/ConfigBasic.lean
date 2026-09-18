import Mathlib.Data.Fintype.Basic
import GroupApproximation.Manuscript.NonMFNotes.Full.Kharlampovich.Forward.StarAlgebra
import GroupApproximation.Manuscript.NonMFNotes.Full.Kharlampovich.Forward.FoldAlgebra

/-!
# Configuration elements as folds of operations in `G(M)`

Input for `thm:fixed-radical-membership` of `non_mf_group_notes.tex`, forward direction of
Kharlampovich--Myasnikov--Sapir (arXiv:1204.6506) Theorem `tmm`(b), equation `(e000)`.

In `G(M)` the configuration word of `(i; m_1, …, m_K)` is the fold
`((x_{q_i A_0} * a_1^{(m_1)}) ⋯ * a_K^{(m_K)}) * A_1 ⋯ * A_K` (`configElem_eq`).  We also
record the relators used in the step argument: small letters commute (G1), the letters
`A_i` commute (G1), letters of different blocks commute (G2), and the machine relators (G8).
-/

namespace GroupApproximation.Full.Kharlampovich

namespace KMS

namespace Forward

section Semiconj

variable {α β ι : Type*}

theorem iterate_semiconj {φ : α → β} {F : α → α} {E : β → β} (h : ∀ x, φ (F x) = E (φ x)) :
    ∀ (m : ℕ) (x : α), φ (F^[m] x) = E^[m] (φ x) := by
  intro m
  induction m with
  | zero => exact fun _ ↦ rfl
  | succ m ih =>
    intro x
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', h, ih]

theorem opFold_semiconj {φ : α → β} {G : ι → α → α} {E : ι → β → β}
    (h : ∀ k x, φ (G k x) = E k (φ x)) : ∀ (L : List ι) (x : α),
      φ (opFold G L x) = opFold E L (φ x) := by
  intro L
  induction L with
  | nil => exact fun _ ↦ rfl
  | cons a L ih =>
    intro x
    rw [opFold_cons, opFold_cons, ih, h]

end Semiconj

section Group

variable {G : Type*} [Group G]

theorem commute_of_khComm_eq_one {u v : G} (h : khComm u v = 1) : Commute u v := by
  have h2 : (v * u)⁻¹ * (u * v) = 1 := by
    rw [mul_inv_rev, ← h]
    simp only [khComm, mul_assoc]
  exact (inv_mul_eq_one.mp h2).symm

end Group

variable {K N : ℕ} (M : Minsky.Machine K N)

/-- The image of a letter in `G(M)`. -/
def lt (s : KhGen K N) : KhGroup M := PresentedGroup.mk (relators M) (FreeGroup.of s)

/-- `f ↦ f * a_{n+1}` in `G(M)`. -/
def sOp (n : Fin K) (f : KhGroup M) : KhGroup M := khStar f (lt M (.a n)) (lt M (.a' n))

/-- `f ↦ f * A_{n+1}` in `G(M)`. -/
def cOp (n : Fin K) (f : KhGroup M) : KhGroup M := khComm f (lt M (.bigA n.succ))

/-- The configuration element as a fold of operations. -/
theorem configElem_eq (c : Minsky.Cfg K N) :
    configElem M c = opFold (cOp M) (List.finRange K)
      (opFold (fun k ↦ (sOp M k)^[c.glass k]) (List.finRange K) (lt M (.x c.state {0}))) := by
  have hc : ∀ (k : Fin K) (x : FreeGroup (KhGen K N)),
      PresentedGroup.mk (relators M) (khComm x (gA k.succ)) =
        cOp M k (PresentedGroup.mk (relators M) x) :=
    fun k x ↦ map_khComm (PresentedGroup.mk (relators M)) x (gA k.succ)
  have hs : ∀ (k : Fin K) (x : FreeGroup (KhGen K N)),
      PresentedGroup.mk (relators M) (khStar x (ga k) (ga' k)) =
        sOp M k (PresentedGroup.mk (relators M) x) :=
    fun k x ↦ map_khStar (PresentedGroup.mk (relators M)) x (ga k) (ga' k)
  have hsi : ∀ (k : Fin K) (x : FreeGroup (KhGen K N)),
      PresentedGroup.mk (relators M)
          ((fun f : FreeGroup (KhGen K N) ↦ khStar f (ga k) (ga' k))^[c.glass k] x) =
        (sOp M k)^[c.glass k] (PresentedGroup.mk (relators M) x) :=
    fun k x ↦ iterate_semiconj (hs k) (c.glass k) x
  have h1 := opFold_semiconj (φ := PresentedGroup.mk (relators M))
    (G := fun (k : Fin K) (x : FreeGroup (KhGen K N)) ↦ khComm x (gA k.succ)) (E := cOp M) hc
    (List.finRange K)
    (opFold (fun (k : Fin K) (x : FreeGroup (KhGen K N)) ↦
      (fun f : FreeGroup (KhGen K N) ↦ khStar f (ga k) (ga' k))^[c.glass k] x)
      (List.finRange K) (gxA0 c.state))
  have h2 := opFold_semiconj (φ := PresentedGroup.mk (relators M))
    (G := fun (k : Fin K) (x : FreeGroup (KhGen K N)) ↦
      (fun f : FreeGroup (KhGen K N) ↦ khStar f (ga k) (ga' k))^[c.glass k] x)
    (E := fun k ↦ (sOp M k)^[c.glass k]) hsi (List.finRange K) (gxA0 c.state)
  rw [h2] at h1
  exact h1

/-! ## Relators -/

theorem commute_lt_of_mem {s t : KhGen K N}
    (h : khComm (FreeGroup.of s) (FreeGroup.of t) ∈ relators M) : Commute (lt M s) (lt M t) :=
  commute_of_khComm_eq_one
    ((map_khComm (PresentedGroup.mk (relators M)) _ _).symm.trans
      (mk_eq_one_of_mem_relators M h))

theorem small_mem_relators {s t : KhGen K N} (hs : s.IsSmall) (ht : t.IsSmall) :
    khComm (FreeGroup.of s) (FreeGroup.of t) ∈ relators M := by
  unfold relators
  refine Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _
    (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _
      (Set.mem_union_left _ (Set.mem_union_left _ ?_))))))))
  unfold g1Relators
  refine Set.mem_union_right _ ?_
  show ∃ s' t' : KhGen K N, s'.IsSmall ∧ t'.IsSmall ∧
    khComm (FreeGroup.of s) (FreeGroup.of t) = khComm (FreeGroup.of s') (FreeGroup.of t')
  exact ⟨s, t, hs, ht, rfl⟩

theorem bigA_mem_relators (i i' : Fin (K + 1)) :
    khComm (gA (N := N) i) (gA i') ∈ relators M := by
  unfold relators
  refine Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _
    (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _
      (Set.mem_union_left _ (Set.mem_union_left _ ?_))))))))
  unfold g1Relators
  refine Set.mem_union_left _ (Set.mem_union_right _ ?_)
  show ∃ j j' : Fin (K + 1), khComm (gA (N := N) i) (gA i') = khComm (gA j) (gA j')
  exact ⟨i, i', rfl⟩

theorem block_mem_relators {s t : KhGen K N} {i i' : Fin (K + 1)} (hs : s.block = some i)
    (ht : t.block = some i') (hii' : i ≠ i') :
    khComm (FreeGroup.of s) (FreeGroup.of t) ∈ relators M := by
  unfold relators
  refine Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _
    (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _
      (Set.mem_union_left _ (Set.mem_union_right _ ?_))))))))
  show ∃ (s' t' : KhGen K N) (j j' : Fin (K + 1)), s'.block = some j ∧ t'.block = some j' ∧
    j ≠ j' ∧ khComm (FreeGroup.of s) (FreeGroup.of t) = khComm (FreeGroup.of s') (FreeGroup.of t')
  exact ⟨s, t, i, i', hs, ht, hii', rfl⟩

theorem commute_a_a (n k : Fin K) : Commute (lt M (.a n)) (lt M (.a k)) :=
  commute_lt_of_mem M (small_mem_relators M trivial trivial)

theorem commute_a_a' (n k : Fin K) : Commute (lt M (.a n)) (lt M (.a' k)) :=
  commute_lt_of_mem M (small_mem_relators M trivial trivial)

theorem commute_a'_a (n k : Fin K) : Commute (lt M (.a' n)) (lt M (.a k)) :=
  commute_lt_of_mem M (small_mem_relators M trivial trivial)

theorem commute_a'_a' (n k : Fin K) : Commute (lt M (.a' n)) (lt M (.a' k)) :=
  commute_lt_of_mem M (small_mem_relators M trivial trivial)

theorem commute_bigA_bigA (i i' : Fin (K + 1)) : Commute (lt M (.bigA i)) (lt M (.bigA i')) :=
  commute_lt_of_mem M (bigA_mem_relators M i i')

theorem commute_bigA_a {n k : Fin K} (h : k ≠ n) :
    Commute (lt M (.bigA n.succ)) (lt M (.a k)) :=
  commute_lt_of_mem M (block_mem_relators M (s := .bigA n.succ) (t := .a k) rfl rfl
    (fun he ↦ h (Fin.succ_inj.mp he.symm)))

theorem commute_bigA_a' {n k : Fin K} (h : k ≠ n) :
    Commute (lt M (.bigA n.succ)) (lt M (.a' k)) :=
  commute_lt_of_mem M (block_mem_relators M (s := .bigA n.succ) (t := .a' k) rfl rfl
    (fun he ↦ h (Fin.succ_inj.mp he.symm)))

/-- G8 for `i → Add(n); j`: `x_{q_i A_0} = x_{q_j A_0} * a_n`. -/
theorem add_relation {i j : Fin (N + 1)} {n : Fin K} (hc : (i, Minsky.Instr.add n j) ∈ M.prog) :
    lt M (.x i {0}) = sOp M n (lt M (.x j {0})) := by
  have h := mk_eq_one_of_mem_relators M (instrRelator_mem_relators M hc)
  have h2 : PresentedGroup.mk (relators M) (gxA0 i) *
      (PresentedGroup.mk (relators M) (khStar (gxA0 j) (ga n) (ga' n)))⁻¹ = 1 := by
    rw [← map_inv, ← map_mul]
    exact h
  rw [map_khStar] at h2
  exact mul_inv_eq_one.mp h2

/-- G8 for `i, ε_n > 0 → Sub(n); j`: `x_{q_i A_0} * a_n = x_{q_j A_0}`. -/
theorem sub_relation {i j : Fin (N + 1)} {n : Fin K} (hc : (i, Minsky.Instr.sub n j) ∈ M.prog) :
    sOp M n (lt M (.x i {0})) = lt M (.x j {0}) := by
  have h := mk_eq_one_of_mem_relators M (instrRelator_mem_relators M hc)
  have h2 : PresentedGroup.mk (relators M) (khStar (gxA0 i) (ga n) (ga' n)) *
      (PresentedGroup.mk (relators M) (gxA0 j))⁻¹ = 1 := by
    rw [← map_inv, ← map_mul]
    exact h
  rw [map_khStar] at h2
  exact mul_inv_eq_one.mp h2

/-- G8 for `i, ε_n = 0 → j`: `x_{q_i A_0} * A_n = x_{q_j A_0} * A_n`. -/
theorem zero_relation {i j : Fin (N + 1)} {n : Fin K}
    (hc : (i, Minsky.Instr.zero n j) ∈ M.prog) :
    cOp M n (lt M (.x i {0})) = cOp M n (lt M (.x j {0})) := by
  have h := mk_eq_one_of_mem_relators M (instrRelator_mem_relators M hc)
  have h2 : PresentedGroup.mk (relators M) (khComm (gxA0 i) (gA n.succ)) *
      (PresentedGroup.mk (relators M) (khComm (gxA0 j) (gA n.succ)))⁻¹ = 1 := by
    rw [← map_inv, ← map_mul]
    exact h
  rw [map_khComm, map_khComm] at h2
  exact mul_inv_eq_one.mp h2

end Forward

end KMS

end GroupApproximation.Full.Kharlampovich
