import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwoWeyl
import GroupApproximation.Meta.AxiomGuard

/-!
# Bruhat cells over `𝔽₂`: the easy steps (lane sk-leavitt-23)

Fix `L` and write `U = colSpan L`, `P = parSpan L`, `S = levSpan L` and `w_j = weyl j L`.
`Bru L g` says that `g ∈ U P` or `g ∈ S w_j P` for some `j ≠ L`.

* `col_split`, `row_split`: split the root `x_jL` (resp. `x_Lj`) off `U` (resp. the row span).
* `col_mul_weyl_mem`: `U w_j ⊆ w_j P`.
* `bru_lev_mul`, `bru_col_mul`: `Bru L` is stable under left multiplication by `S` and by `U`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo

open GroupApproximation.SteinbergGroup

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem zmod_two_cases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo.zmod_two_cases

theorem col_split {j L : I} (hj : j ≠ L) {u : SteinbergGroup I (ZMod 2)} (hu : u ∈ colSpan L) :
    ∃ d : ZMod 2, ∃ u' ∈ rootSpan (R := ZMod 2) (fun i k => k = L ∧ i ≠ j),
      u = x j L hj d * u' :=
  exists_split (p := fun _ k => k = L) (q := fun i k => k = L ∧ i ≠ j) hj
    (fun i k _ (hk : k = L) => by
      by_cases hij : i = j
      · exact Or.inl ⟨hij, hk⟩
      · exact Or.inr ⟨hk, hij⟩)
    (fun i k h a c (hq : k = L ∧ i ≠ j) => x_commute_of_ne j L i k hj h
      (by rw [← hq.1]; exact h.symm) (by rw [hq.1]; exact hj.symm) c a) hu

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo.col_split

theorem row_split {j L : I} (hj : j ≠ L) {v : SteinbergGroup I (ZMod 2)} (hv : v ∈ rowSpan L) :
    ∃ d : ZMod 2, ∃ v' ∈ rootSpan (R := ZMod 2) (fun i k => i = L ∧ k ≠ j),
      v = x L j hj.symm d * v' :=
  exists_split (p := fun i _ => i = L) (q := fun i k => i = L ∧ k ≠ j) hj.symm
    (fun i k _ (hi : i = L) => by
      by_cases hkj : k = j
      · exact Or.inl ⟨hi, hkj⟩
      · exact Or.inr ⟨hi, hkj⟩)
    (fun i k h a c (hq : i = L ∧ k ≠ j) => x_commute_of_ne L j i k hj.symm h
      (by rw [hq.1]; exact hj) (by rw [← hq.1]; exact h.symm) c a) hv

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo.row_split

theorem weyl_mul_conj {j L : I} (hj : j ≠ L) (g : SteinbergGroup I (ZMod 2)) :
    g * weyl j L hj = weyl j L hj * (weyl j L hj * g * (weyl j L hj)⁻¹) := by
  rw [weyl_inv two_eq_zero, ← mul_assoc, ← mul_assoc, weyl_mul_self two_eq_zero, one_mul]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo.weyl_mul_conj

/-- `U w_j ⊆ w_j P`. -/
theorem col_mul_weyl_mem (hthird : ∀ a b : I, ∃ m : I, m ≠ a ∧ m ≠ b) {j L : I} (hj : j ≠ L)
    {u : SteinbergGroup I (ZMod 2)} (hu : u ∈ colSpan L) :
    ∃ p ∈ parSpan L, u * weyl j L hj = weyl j L hj * p := by
  obtain ⟨d, u', hu', rfl⟩ := col_split hj hu
  have hC : weyl j L hj * u' * (weyl j L hj)⁻¹ ∈ parSpan L :=
    lev_le_par (weyl_conj_colExcept hthird hj hu')
  rcases zmod_two_cases d with rfl | rfl
  · refine ⟨_, hC, ?_⟩
    rw [x_zero, one_mul]
    exact weyl_mul_conj hj u'
  · refine ⟨x L j hj.symm 1 * (weyl j L hj * u' * (weyl j L hj)⁻¹),
      Subgroup.mul_mem _ (x_mem_rootSpan (p := fun _ k => k ≠ L) hj.symm (1 : ZMod 2) hj) hC, ?_⟩
    rw [mul_assoc, weyl_mul_conj hj u', ← mul_assoc, col_mul_weyl hthird hj, mul_assoc]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo.col_mul_weyl_mem

/-- The two Bruhat cells `U P` and `S w_j P` (`j ≠ L`). -/
def Bru (L : I) (g : SteinbergGroup I (ZMod 2)) : Prop :=
  (∃ u ∈ colSpan L, ∃ p ∈ parSpan L, g = u * p) ∨
    ∃ (j : I) (hj : j ≠ L), ∃ s ∈ levSpan L, ∃ p ∈ parSpan L, g = s * weyl j L hj * p

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo.Bru

theorem bru_one (L : I) : Bru L (1 : SteinbergGroup I (ZMod 2)) :=
  Or.inl ⟨1, Subgroup.one_mem _, 1, Subgroup.one_mem _, (mul_one 1).symm⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo.bru_one

theorem bru_lev_mul {L : I} {t g : SteinbergGroup I (ZMod 2)} (ht : t ∈ levSpan L)
    (hg : Bru L g) : Bru L (t * g) := by
  rcases hg with ⟨u, hu, p, hp, rfl⟩ | ⟨j, hj, s, hs, p, hp, rfl⟩
  · exact Or.inl ⟨t * u * t⁻¹, lev_conj_col ht hu, t * p,
      Subgroup.mul_mem _ (lev_le_par ht) hp, by group⟩
  · exact Or.inr ⟨j, hj, t * s, Subgroup.mul_mem _ ht hs, p, hp, by simp only [mul_assoc]⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo.bru_lev_mul

theorem bru_col_mul (hthird : ∀ a b : I, ∃ m : I, m ≠ a ∧ m ≠ b) {L : I}
    {t g : SteinbergGroup I (ZMod 2)} (ht : t ∈ colSpan L) (hg : Bru L g) : Bru L (t * g) := by
  rcases hg with ⟨u, hu, p, hp, rfl⟩ | ⟨j, hj, s, hs, p, hp, rfl⟩
  · exact Or.inl ⟨t * u, Subgroup.mul_mem _ ht hu, p, hp, by simp only [mul_assoc]⟩
  · have ht' : s⁻¹ * t * s ∈ colSpan L := by
      have h := lev_conj_col (Subgroup.inv_mem _ hs) ht
      rwa [inv_inv] at h
    obtain ⟨p', hp', e⟩ := col_mul_weyl_mem hthird hj ht'
    refine Or.inr ⟨j, hj, s, hs, p' * p, Subgroup.mul_mem _ hp' hp, ?_⟩
    calc t * (s * weyl j L hj * p) = s * (s⁻¹ * t * s * weyl j L hj) * p := by group
      _ = s * (weyl j L hj * p') * p := by rw [e]
      _ = s * weyl j L hj * (p' * p) := by simp only [mul_assoc]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo.bru_col_mul

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo
