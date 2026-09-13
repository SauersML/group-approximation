import GroupApproximation.ThompsonOre.ThompsonF
import GroupApproximation.GroupTheory.HigmanThompson.PLMoves

/-!
# The shift of Thompson's group `F` and the subgroup fixing `(-∞, 1]`

Conjugation by the translation `t ↦ t + 1` carries `X_k` to `X_{k+1}`, so it realizes the
shift `x_k ↦ x_{k+1}` on `F` through the faithful action `ev`.  The image of the shift is the
subgroup `halfFix` of elements fixing `(-∞, 1]`, which contains `x₁`, and the inverse of the
shift is an isomorphism `halfFix ≃* F` sending `x₁` to `x₀`.  The conjugates of `halfFix` are
nested: for every `c`, either `c halfFix c⁻¹ ≤ halfFix` or `c⁻¹ halfFix c ≤ halfFix`.
-/

namespace GroupApproximation
namespace ThompsonOre

open HigmanThompson

noncomputable section

/-- Conjugation by the translation `t ↦ t + 1`. -/
def conjT : Equiv.Perm ℚ →* Equiv.Perm ℚ :=
  (MulAut.conj (transPerm 1)).toMonoidHom

theorem conjT_eq (f : Equiv.Perm ℚ) : conjT f = transPerm 1 * f * (transPerm 1)⁻¹ := rfl

theorem conjT_apply (f : Equiv.Perm ℚ) (t : ℚ) : conjT f t = f (t - 1) + 1 := rfl

theorem conjT_injective : Function.Injective conjT :=
  (MulAut.conj (transPerm 1)).injective

theorem conjT_xg (k : ℕ) : conjT (xg 0 k) = xg 0 (k + 1) := by
  ext t
  simp only [conjT_apply, xg_apply, xfun]
  push_cast
  split_ifs <;> linarith

theorem conjT_ev_xn (k : ℕ) : conjT (ev (xn k)) = ev (xn (k + 1)) := by
  rw [ev_xn, ev_xn, map_inv, conjT_xg]

/-! ## The shift -/

theorem shift_rel_one :
    (xn 1 ^ 2)⁻¹ * xn 2 * xn 1 ^ 2 = (xn 1 * xn 2)⁻¹ * xn 2 * (xn 1 * xn 2) := by
  apply ev_injective
  simpa only [map_mul, map_inv, map_pow, ← xn_zero, ← xn_one, conjT_ev_xn] using
    congrArg (fun g => conjT (ev g)) rel_one

theorem shift_rel_two :
    (xn 1 ^ 3)⁻¹ * xn 2 * xn 1 ^ 3 = (xn 1 ^ 2 * xn 2)⁻¹ * xn 2 * (xn 1 ^ 2 * xn 2) := by
  apply ev_injective
  simpa only [map_mul, map_inv, map_pow, ← xn_zero, ← xn_one, conjT_ev_xn] using
    congrArg (fun g => conjT (ev g)) rel_two

/-- The shift endomorphism `x_k ↦ x_{k+1}`. -/
def shift : ThompsonF →* ThompsonF :=
  PresentedGroup.toGroup (f := fun i : Fin 2 => xn (i.val + 1))
    (lift_thompsonRels (fun i : Fin 2 => xn (i.val + 1)) shift_rel_one shift_rel_two)

theorem shift_of (i : Fin 2) : shift (PresentedGroup.of i) = xn (i.val + 1) :=
  PresentedGroup.toGroup.of _

theorem ev_comp_shift : ev.comp shift = conjT.comp ev :=
  PresentedGroup.ext fun i => by
    show ev (shift (PresentedGroup.of i)) = conjT (ev (PresentedGroup.of i))
    rw [shift_of, ← xn_of, conjT_ev_xn]

/-- The shift is conjugation by `t ↦ t + 1` on the action. -/
theorem ev_shift (g : ThompsonF) : ev (shift g) = conjT (ev g) :=
  DFunLike.congr_fun ev_comp_shift g

theorem shift_xn (k : ℕ) : shift (xn k) = xn (k + 1) :=
  ev_injective (by rw [ev_shift, conjT_ev_xn])

theorem shift_x0 : shift x0 = x1 :=
  (shift_xn 0).trans xn_one

theorem shift_injective : Function.Injective shift := fun a b h => by
  have e := congrArg ev h
  rw [ev_shift, ev_shift] at e
  exact ev_injective (conjT_injective e)

/-! ## The subgroup fixing `(-∞, 1]` -/

/-- The elements of `F` fixing `(-∞, 1]`. -/
def halfFix : Subgroup ThompsonF where
  carrier := {g | ∀ t : ℚ, t ≤ 1 → ev g t = t}
  mul_mem' {a b} ha hb t ht := by
    rw [map_mul, Equiv.Perm.mul_apply, hb t ht, ha t ht]
  one_mem' t _ := by
    rw [map_one, Equiv.Perm.one_apply]
  inv_mem' {a} ha t ht := by
    rw [map_inv, Equiv.Perm.inv_eq_iff_eq, ha t ht]

theorem mem_halfFix {g : ThompsonF} : g ∈ halfFix ↔ ∀ t : ℚ, t ≤ 1 → ev g t = t :=
  Iff.rfl

theorem x1_mem_halfFix : x1 ∈ halfFix := mem_halfFix.mpr fun t ht => by
  rw [← xn_one, ev_xn]
  exact xg_inv_of_le 0 (by exact_mod_cast ht)

/-- The image of the shift is `halfFix`. -/
theorem shift_range_eq : shift.range = halfFix := by
  ext g
  rw [MonoidHom.mem_range, mem_halfFix]
  constructor
  · rintro ⟨h, rfl⟩ t ht
    rw [ev_shift, conjT_apply, ev_fix h (t := t - 1) (by linarith)]
    ring
  · intro hg
    have hT := transPerm_mem 0 (one_mem_grid_mTwo 0 0)
    obtain ⟨T, c, hc⟩ := (ev_mem_geoF g).2.2
    have hf : (transPerm 1)⁻¹ * ev g * transPerm 1 ∈ geoF 0 := by
      refine ⟨mul_mem (mul_mem (inv_mem hT) (ev_mem_geoF g).1) hT, fun t ht => ?_, T, c,
        fun t ht => ?_⟩
      · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, transPerm_apply,
          hg (t + 1) (by linarith), transPerm_inv_apply]
        ring
      · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, transPerm_apply,
          hc (t + 1) (by linarith), transPerm_inv_apply]
        ring
    obtain ⟨h, hh⟩ := exists_ev_eq hf
    refine ⟨h, ev_injective ?_⟩
    rw [ev_shift, hh, conjT_eq]
    group

/-- `halfFix ≃* F`, the inverse of the shift. -/
def halfFixEquiv : halfFix ≃* ThompsonF :=
  ((MonoidHom.ofInjective shift_injective).trans (MulEquiv.subgroupCongr shift_range_eq)).symm

theorem halfFixEquiv_x1 : halfFixEquiv ⟨x1, x1_mem_halfFix⟩ = x0 := by
  rw [halfFixEquiv, MulEquiv.symm_apply_eq]
  exact Subtype.ext shift_x0.symm

/-- The conjugates of `halfFix` are nested. -/
theorem halfFix_conj_chain (c : ThompsonF) :
    (∀ f ∈ halfFix, c * f * c⁻¹ ∈ halfFix) ∨ (∀ f ∈ halfFix, c⁻¹ * f * c ∈ halfFix) := by
  rcases le_or_gt (ev c⁻¹ 1) 1 with h | h
  · refine Or.inl fun f hf => mem_halfFix.mpr fun t ht => ?_
    have h1 : ev c⁻¹ t ≤ 1 := ((ev_strictMono c⁻¹).monotone ht).trans h
    rw [map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, mem_halfFix.mp hf _ h1,
      map_inv, perm_apply_inv_self]
  · refine Or.inr fun f hf => mem_halfFix.mpr fun t ht => ?_
    have h2 : ev c 1 < 1 := by
      have e := ev_strictMono c h
      rwa [map_inv, perm_apply_inv_self] at e
    have h1 : ev c t ≤ 1 := ((ev_strictMono c).monotone ht).trans h2.le
    rw [map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, mem_halfFix.mp hf _ h1,
      map_inv, perm_inv_apply_self]

end

end ThompsonOre
end GroupApproximation
