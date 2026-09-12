import GroupApproximation.GroupTheory.HydeLodha.QTwoFinitePresentationSlopes
import GroupApproximation.GroupTheory.HigmanThompson.RstabIso
import GroupApproximation.Meta.AxiomGuard

/-!
# `Υ_Γ(I)` for `|I| < 1`

Hyde–Lodha, proof of Lemma 4.5, first case: "If `b - a < 1`, then there is an `f ∈ Γ_n` such that
`I = [a, b]·f ⊂ (0, 1)`.  It follows that `Υ_{Γ_n}([a, b]) ≅ Υ_{Γ_n}(I) = Υ_{F_{η_n}}(I) ≅ F_{η_n}`."

* `upsilon_mono`, `map_conj_upsilon`, `upsilonConjEquiv`: for `Q₂ ≤ Γ ≤ Γ₂` and `g ∈ Γ₂`, conjugation
  by `g` is an isomorphism `Υ_Γ([a, b]) ≃* Υ_Γ([g a, g b])`;
* `upsilon_gammaTwo_eq_map`: for `0 < a < b < 1`, `Υ_{Γ₂}([a, b])` is the periodic copy of
  `Rstab_{F_6}([a, b])`, so `isFinitelyPresented_upsilon_gammaTwo_unit`;
* `isFinitelyPresented_upsilon_gammaTwo_short`: `Υ_{Γ₂}([a, b])` is finitely presented whenever
  `a < b` are in `ℤ[1/6]` with `b - a < 1` (moved into `(0, 1)` by `exists_move_into_unit`).
-/

namespace GroupApproximation
namespace HydeLodha

open HigmanThompson

theorem upsilon_mono {Γ Γ' : Subgroup (Equiv.Perm ℚ)} (hΓ : Γ ≤ Γ') {a b a₂ b₂ : ℚ}
    (h : perIoo a₂ b₂ ⊆ perIoo a b) : upsilon Γ a₂ b₂ ≤ upsilon Γ' a b := by
  intro f hf
  obtain ⟨hfΓ, hfs⟩ := mem_upsilon.mp hf
  exact mem_upsilon.mpr ⟨hΓ hfΓ, hfs.mono h⟩

/-! ## Conjugation -/

theorem map_conj_upsilon {Γ : Subgroup (Equiv.Perm ℚ)} (hQ : qTwo ≤ Γ) (hΓ : Γ ≤ gammaTwo)
    {g : Equiv.Perm ℚ} (hg : g ∈ gammaTwo) (a b : ℚ) :
    (upsilon Γ a b).map (MulAut.conj g).toMonoidHom = upsilon Γ (g a) (g b) := by
  have hnorm := normalized_of_qTwo_le hQ hΓ
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact conj_mem_upsilon hg (fun y hy => hnorm y hy g hg) hx
  · intro y hy
    have hgi : g⁻¹ ∈ gammaTwo := gammaTwo.inv_mem hg
    have hx := conj_mem_upsilon hgi (fun z hz => hnorm z hz g⁻¹ hgi) hy
    rw [perm_inv_apply_self, perm_inv_apply_self] at hx
    refine ⟨g⁻¹ * y * g⁻¹⁻¹, hx, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

/-- **Conjugation `Υ_Γ([a, b]) ≃* Υ_Γ([g a, g b])`.** -/
noncomputable def upsilonConjEquiv {Γ : Subgroup (Equiv.Perm ℚ)} (hQ : qTwo ≤ Γ)
    (hΓ : Γ ≤ gammaTwo) {g : Equiv.Perm ℚ} (hg : g ∈ gammaTwo) (a b : ℚ) :
    upsilon Γ a b ≃* upsilon Γ (g a) (g b) :=
  ((upsilon Γ a b).equivMapOfInjective (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).trans (MulEquiv.subgroupCongr (map_conj_upsilon hQ hΓ hg a b))

/-! ## The unit frame -/

theorem not_mem_perIoo_of_unit {a b t : ℚ} (h0a : 0 < a) (hb1 : b < 1) (h0t : 0 ≤ t) (ht1 : t < 1)
    (ht : t ≤ a ∨ b ≤ t) : t ∉ perIoo a b := by
  rintro ⟨k, hk1, hk2⟩
  rcases lt_trichotomy k 0 with hk | hk | hk
  · have hk' : (k : ℚ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
    linarith
  · rw [hk, Int.cast_zero, add_zero] at hk1 hk2
    rcases ht with ht | ht <;> linarith
  · have hk' : (1 : ℚ) ≤ k := by exact_mod_cast hk
    linarith

theorem upsilon_gammaTwo_eq_map {a b : ℚ} (h0a : 0 < a) (hab : a < b) (hb1 : b < 1) :
    upsilon gammaTwo a b = ((rstab 4 a b).subgroupOf (compactF 4 1)).map (perHom 4) := by
  apply le_antisymm
  · intro f hf
    obtain ⟨hfΓ, hfs⟩ := mem_upsilon.mp hf
    have h0 : f 0 = 0 := hfs 0 (not_mem_perIoo_of_unit h0a hb1 le_rfl zero_lt_one (Or.inl h0a.le))
    obtain ⟨x, rfl⟩ := mem_range_perHom_of_fix_zero hfΓ h0
    refine ⟨x, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
    have hval : ∀ t : ℚ, 0 ≤ t → t < 1 → (x : Equiv.Perm ℚ) t = perHom 4 x t :=
      fun t h0t ht1 => (perHom_apply_of_mem 4 x h0t ht1).symm
    show (x : Equiv.Perm ℚ) ∈ PLGroup (4 + 2) (powSlopes 4) ∧
      (∀ t : ℚ, t ≤ a → (x : Equiv.Perm ℚ) t = t) ∧ ∀ t : ℚ, b ≤ t → (x : Equiv.Perm ℚ) t = t
    refine ⟨x.2.1, fun t ht => ?_, fun t ht => ?_⟩
    · rcases le_or_gt t 0 with ht0 | ht0
      · exact compactF_fix_nonpos x.2 ht0
      · rw [hval t ht0.le (by linarith)]
        exact hfs t (not_mem_perIoo_of_unit h0a hb1 ht0.le (by linarith) (Or.inl ht))
    · rcases le_or_gt 1 t with ht1 | ht1
      · exact compactF_fix_one x.2 ht1
      · rw [hval t (by linarith) ht1]
        exact hfs t (not_mem_perIoo_of_unit h0a hb1 (by linarith) ht1 (Or.inr ht))
  · rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hx
    obtain ⟨-, hxa, hxb⟩ := hx
    have hs : SupportedIn (x : Equiv.Perm ℚ) (Set.Ioo a b) := by
      intro t ht
      rcases le_or_gt t a with h | h
      · exact hxa t h
      · exact hxb t (by by_contra hc; exact ht ⟨h, not_le.mp hc⟩)
    exact mem_upsilon.mpr ⟨perHom_mem_gammaTwo x,
      (supportedIn_perHom 4 (f := x) hs).mono (perSet_Ioo_subset a b)⟩

/-- **`Υ_{Γ₂}([a, b]) ≅ Rstab_{F_6}([a, b])`** in the unit frame. -/
noncomputable def rstabEquivUpsilon {a b : ℚ} (h0a : 0 < a) (hab : a < b) (hb1 : b < 1) :
    rstab 4 a b ≃* upsilon gammaTwo a b :=
  (Subgroup.subgroupOfEquivOfLe (rstab_le_compactF_one (m := 4) h0a.le hb1.le)).symm.trans
    ((((rstab 4 a b).subgroupOf (compactF 4 1)).equivMapOfInjective (perHom 4)
      (perHom_injective 4)).trans (MulEquiv.subgroupCongr (upsilon_gammaTwo_eq_map h0a hab hb1).symm))

theorem isFinitelyPresented_upsilon_gammaTwo_unit {a b : ℚ} (ha : ∃ M, a ∈ Grid 6 M)
    (hb : ∃ M, b ∈ Grid 6 M) (h0a : 0 < a) (hab : a < b) (hb1 : b < 1) :
    Group.IsFinitelyPresented ↥(upsilon gammaTwo a b) := by
  haveI := isFinitelyPresented_rstab (m := 4) ha hb hab
  exact Group.IsFinitelyPresented.equiv (rstabEquivUpsilon h0a hab hb1)

/-- **Hyde–Lodha, Lemma 4.5, first case.** -/
theorem isFinitelyPresented_upsilon_gammaTwo_short {a b : ℚ} (ha : ∃ M, a ∈ Grid 6 M)
    (hb : ∃ M, b ∈ Grid 6 M) (hab : a < b) (hba : b - a < 1) :
    Group.IsFinitelyPresented ↥(upsilon gammaTwo a b) := by
  obtain ⟨g, hg, j, hj0, hj1⟩ := exists_move_into_unit ha hb hab hba
  have hgmono := gammaTwo_strictMono hg
  obtain ⟨Ma, hMa⟩ := gammaTwo_apply_grid hg ha
  obtain ⟨Mb, hMb⟩ := gammaTwo_apply_grid hg hb
  have hgaG : ∃ M, g a + j ∈ Grid 6 M := ⟨Ma, grid_add hMa (int_mem_grid Ma j)⟩
  have hgbG : ∃ M, g b + j ∈ Grid 6 M := ⟨Mb, grid_add hMb (int_mem_grid Mb j)⟩
  haveI := isFinitelyPresented_upsilon_gammaTwo_unit hgaG hgbG hj0
    (by have := hgmono hab; linarith) hj1
  have e : upsilon gammaTwo (g a + j) (g b + j) = upsilon gammaTwo (g a) (g b) :=
    upsilon_add_int gammaTwo (g a) (g b) j
  haveI : Group.IsFinitelyPresented ↥(upsilon gammaTwo (g a) (g b)) :=
    Group.IsFinitelyPresented.equiv (MulEquiv.subgroupCongr e)
  exact Group.IsFinitelyPresented.equiv
    (upsilonConjEquiv qTwo_le_gammaTwo le_rfl hg a b).symm

#audit_axioms GroupApproximation.HydeLodha.map_conj_upsilon
#audit_axioms GroupApproximation.HydeLodha.upsilon_gammaTwo_eq_map
#audit_axioms GroupApproximation.HydeLodha.isFinitelyPresented_upsilon_gammaTwo_unit
#audit_axioms GroupApproximation.HydeLodha.isFinitelyPresented_upsilon_gammaTwo_short

end HydeLodha
end GroupApproximation
