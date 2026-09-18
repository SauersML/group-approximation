import GroupApproximation.Manuscript.NonMFNotes.Full.Kharlampovich.Solvable.KhRel
import GroupApproximation.Manuscript.NonMFNotes.Full.Kharlampovich.Solvable.BRMulti

/-!
# Conjugates of `x`-letters by the letters `a_n, a'_n` commute

Input for `thm:fixed-radical-membership` of `non_mf_group_notes.tex`: a step of
Kharlampovich--Myasnikov--Sapir (arXiv:1204.6506) Lemma `lT`.  For `g, h` in the subgroup
`⟨a_n, a'_n⟩` of `G(M)` and any `x`-letters `x_u, x_v`, the conjugates `x_u^g` and `x_v^h`
commute (`commute_conj_aSub`).  This is `BR.multi_commute` for the letters `a_n⁻¹, (a'_n)⁻¹`:
G5 b) or G5 c) gives the action hypothesis, and G7 gives the base case.
-/

namespace GroupApproximation.Full.Kharlampovich

namespace KMS

namespace Sol

open Forward

variable {K N : ℕ} (M : Minsky.Machine K N)

/-- The letter `a_n⁻¹`. -/
def ia (n : Fin K) : KhGroup M := (kLet M (.a n))⁻¹

/-- The letter `(a'_n)⁻¹`. -/
def ia' (n : Fin K) : KhGroup M := (kLet M (.a' n))⁻¹

/-- The `x`-letter indexed by a pair `(j, S)`. -/
def xl (q : Fin (N + 1) × Finset (Fin (K + 1))) : KhGroup M := kLet M (.x q.1 q.2)

/-- The subgroup `⟨a_n, a'_n⟩` of `G(M)`. -/
def aSub : Subgroup (KhGroup M) :=
  Subgroup.closure (Set.range (fun n => kLet M (.a n)) ∪ Set.range (fun n => kLet M (.a' n)))

theorem a_mem_aSub (n : Fin K) : kLet M (.a n) ∈ aSub M :=
  Subgroup.subset_closure (Set.mem_union_left _ ⟨n, rfl⟩)

theorem a'_mem_aSub (n : Fin K) : kLet M (.a' n) ∈ aSub M :=
  Subgroup.subset_closure (Set.mem_union_right _ ⟨n, rfl⟩)

theorem hl_ia (n m : Fin K) :
    Commute (ia M n) (ia M m) ∧ Commute (ia M n) (ia' M m) ∧ Commute (ia' M n) (ia' M m) :=
  ⟨(commute_a_a M n m).inv_inv, (commute_a_a' M n m).inv_inv, (commute_a'_a' M n m).inv_inv⟩

/-- G5 b) (active glass) or G5 c) (inert glass). -/
theorem hact_ia (q : Fin (N + 1) × Finset (Fin (K + 1))) (n : Fin K) :
    ia' M n * xl M q * (ia' M n)⁻¹ = ia M n * xl M q * (ia M n)⁻¹ * (xl M q)⁻¹ ∨
      (Commute (xl M q) (ia M n) ∧ Commute (xl M q) (ia' M n)) := by
  by_cases hn : n.succ ∈ q.2
  · exact Or.inr ⟨(commute_x_block M q.1 (s := .a n) hn rfl).inv_right,
      (commute_x_block M q.1 (s := .a' n) hn rfl).inv_right⟩
  · left
    simp only [ia, ia', inv_inv]
    exact (x_conj_a M q.1 q.2 hn).symm

/-- The exponent vector `α = 1 - β` of G7. -/
def alphaOf (β : Fin K → ℤ) (hβ : ∀ n, -1 ≤ β n ∧ β n ≤ 1) : Fin K → Fin 3 :=
  fun n => ⟨(1 - β n).toNat, by obtain ⟨h1, h2⟩ := hβ n; omega⟩

/-- `a_1^{-β_1} ⋯ a_K^{-β_K}` is the image of the word `zword ga (1 - β)` of G7. -/
theorem pw_ia_eq (β : Fin K → ℤ) (hβ : ∀ n, -1 ≤ β n ∧ β n ≤ 1) :
    BR.pw (ia M) (ia' M) β 0 = PresentedGroup.mk (relators M) (zword ga (alphaOf β hβ)) := by
  rw [mk_zword, BR.pw_eq_foldl]
  congr 1
  funext g n
  have he : (((alphaOf β hβ n).val : ℤ) - 1) = -β n := by
    obtain ⟨h1, h2⟩ := hβ n
    show (((1 - β n).toNat : ℕ) : ℤ) - 1 = -β n
    omega
  show g * ((kLet M (.a n))⁻¹ ^ β n * (kLet M (.a' n))⁻¹ ^ (0 : ℤ)) =
    g * kLet M (.a n) ^ (((alphaOf β hβ n).val : ℤ) - 1)
  rw [he, zpow_zero, mul_one, inv_zpow']

/-- G7 as the base case of `BR.multi_commute`. -/
theorem hbase_ia (q q' : Fin (N + 1) × Finset (Fin (K + 1))) (β : Fin K → ℤ)
    (hβ : ∀ n, -1 ≤ β n ∧ β n ≤ 1) :
    Commute ((BR.pw (ia M) (ia' M) β 0)⁻¹ * xl M q * BR.pw (ia M) (ia' M) β 0) (xl M q') := by
  rw [pw_ia_eq M β hβ]
  exact commute_g7 M q.1 q'.1 q.2 q'.2 (alphaOf β hβ)

theorem commute_pw_conj (q q' : Fin (N + 1) × Finset (Fin (K + 1)))
    (β γ β' γ' : Fin K → ℤ) :
    Commute ((BR.pw (ia M) (ia' M) β γ)⁻¹ * xl M q * BR.pw (ia M) (ia' M) β γ)
      ((BR.pw (ia M) (ia' M) β' γ')⁻¹ * xl M q' * BR.pw (ia M) (ia' M) β' γ') :=
  BR.multi_commute (ia M) (ia' M) (xl M) (hl_ia M) (hact_ia M) (hbase_ia M) q q' β γ β' γ'

theorem exists_pw_ia {g : KhGroup M} (hg : g ∈ aSub M) :
    ∃ β γ : Fin K → ℤ, g = BR.pw (ia M) (ia' M) β γ := by
  obtain ⟨β, γ, rfl⟩ := BR.exists_pw_of_mem_closure (fun n => kLet M (.a n))
    (fun n => kLet M (.a' n))
    (fun n m => ⟨commute_a_a M n m, commute_a_a' M n m, commute_a'_a' M n m⟩) hg
  refine ⟨-β, -γ, BR.lprod_congr (fun n => ?_) _⟩
  show kLet M (.a n) ^ β n * kLet M (.a' n) ^ γ n =
    (kLet M (.a n))⁻¹ ^ (-β n) * (kLet M (.a' n))⁻¹ ^ (-γ n)
  rw [inv_zpow', inv_zpow', neg_neg, neg_neg]

/-- Lemma `lT`, `a`-letter part: `[x_u^g, x_v^h] = 1` for `g, h ∈ ⟨a_n, a'_n⟩`. -/
theorem commute_conj_aSub {g h : KhGroup M} (hg : g ∈ aSub M) (hh : h ∈ aSub M)
    (j j' : Fin (N + 1)) (S S' : Finset (Fin (K + 1))) :
    Commute (g⁻¹ * kLet M (.x j S) * g) (h⁻¹ * kLet M (.x j' S') * h) := by
  obtain ⟨β, γ, rfl⟩ := exists_pw_ia M hg
  obtain ⟨β', γ', rfl⟩ := exists_pw_ia M hh
  exact commute_pw_conj M (j, S) (j', S') β γ β' γ'

end Sol

end KMS

end GroupApproximation.Full.Kharlampovich
