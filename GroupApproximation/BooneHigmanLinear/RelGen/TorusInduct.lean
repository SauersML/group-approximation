import GroupApproximation.BooneHigmanLinear.RelGen.TorusFaith
import GroupApproximation.Meta.AxiomGuard

/-!
# The torus meets `K₂` only in symbols: the induction

Lane bh-pal-wire, k2-poly H.L1 (ii). See `TorusFaith` for the plan.

* `torusSL K hmL = {t' h_mL(c) : t' ∈ T_K}`, and every generator of `T_{K ∪ {L}}` (and its inverse)
  maps it into itself under left multiplication (`SL_mul_h`, `SL_mul_gen_inv`).
* `torusK_insert_subset`: `T_{K ∪ {L}} ⊆ torusSL K hmL`.
* **`torus_faith`**: an element of `T_K` acting trivially on `R^I` lies in the symbol subgroup.
-/

namespace GroupApproximation.BooneHigmanLinear.RelGen

open GroupApproximation.SteinbergGroup
open GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl (h)
open GroupApproximation.BooneHigmanLinear.K2Poly (csym)
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo (act unitVec
  unitVec_apply act_mul)

variable {I : Type*} [Fintype I] [DecidableEq I] {R : Type*} [CommRing R]

variable (R) in
/-- `T_K · h_mL(Rˣ)`. -/
def torusSL (K : Finset I) {m L : I} (hmL : m ≠ L) : Set (SteinbergGroup I R) :=
  {g | ∃ t ∈ torusK I R K, ∃ c : Rˣ, g = t * h m L hmL c}

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.torusSL

section Absorb

variable {K : Finset I} {m L : I} (hmL : m ≠ L)

theorem SL_mul_torusK {t : SteinbergGroup I R} (ht : t ∈ torusK I R K) {y : SteinbergGroup I R}
    (hy : y ∈ torusSL R K hmL) : t * y ∈ torusSL R K hmL := by
  obtain ⟨t', ht', c, rfl⟩ := hy
  exact ⟨t * t', Subgroup.mul_mem _ ht ht', c, by group⟩

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.SL_mul_torusK

variable (third : ThirdIndex I) (hLK : L ∉ K)
include third hLK

theorem SL_mul_hmL (u : Rˣ) {y : SteinbergGroup I R} (hy : y ∈ torusSL R K hmL) :
    h m L hmL u * y ∈ torusSL R K hmL := by
  obtain ⟨t', ht', c, rfl⟩ := hy
  refine ⟨h m L hmL u * t' * (h m L hmL u)⁻¹ * (csym m L hmL c u)⁻¹,
    Subgroup.mul_mem _ (hmL_conj_torusK third hLK hmL u ht')
      (Subgroup.inv_mem _ (symGroup_le_torusK K (csym_mem_symGroup hmL c u))), c * u, ?_⟩
  rw [show h m L hmL u * t' * (h m L hmL u)⁻¹ * (csym m L hmL c u)⁻¹ * h m L hmL (c * u) =
    h m L hmL u * t' * (h m L hmL u)⁻¹ * ((csym m L hmL c u)⁻¹ * h m L hmL (c * u)) by group,
    ← h_mul_h]
  group

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.SL_mul_hmL

variable (hm : m ∈ K)
include hm

theorem SL_mul_haL {a : I} (ha : a ∈ K) (haL : a ≠ L) (v : Rˣ) {y : SteinbergGroup I R}
    (hy : y ∈ torusSL R K hmL) : h a L haL v * y ∈ torusSL R K hmL := by
  by_cases ham : a = m
  · subst ham
    exact SL_mul_hmL hmL third hLK v hy
  · rw [show h a L haL v = (csym a L haL (-1) v)⁻¹ * (h a m ham v * h m L hmL v) by
      rw [h_mul_h_third ham hmL haL v]; group, mul_assoc, mul_assoc]
    exact SL_mul_torusK hmL (Subgroup.inv_mem _ (symGroup_le_torusK K (csym_mem_symGroup _ _ _)))
      (SL_mul_torusK hmL (h_mem_torusK ham ha hm v) (SL_mul_hmL hmL third hLK v hy))

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.SL_mul_haL

theorem SL_mul_hLa {a : I} (ha : a ∈ K) (hLa : L ≠ a) (v : Rˣ) {y : SteinbergGroup I R}
    (hy : y ∈ torusSL R K hmL) : h L a hLa v * y ∈ torusSL R K hmL := by
  obtain ⟨k, hak, hLk⟩ := third a L
  rw [h_swap hLa.symm k hak hLk v, mul_assoc]
  exact SL_mul_torusK hmL (symGroup_le_torusK K (csym_mem_symGroup _ _ _))
    (SL_mul_haL hmL third hLK hm ha hLa.symm v⁻¹ hy)

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.SL_mul_hLa

/-- Left multiplication by `h_ab(u)`, `a, b ∈ K ∪ {L}`, preserves `torusSL`. -/
theorem SL_mul_h {a b : I} (hab : a ≠ b) (ha : a ∈ insert L K) (hb : b ∈ insert L K) (u : Rˣ)
    {y : SteinbergGroup I R} (hy : y ∈ torusSL R K hmL) : h a b hab u * y ∈ torusSL R K hmL := by
  rcases Finset.mem_insert.mp ha with haL | haK
  · subst haL
    rcases Finset.mem_insert.mp hb with hbL | hbK
    · exact absurd hbL.symm hab
    · exact SL_mul_hLa hmL third hLK hm hbK hab u hy
  · rcases Finset.mem_insert.mp hb with hbL | hbK
    · subst hbL
      exact SL_mul_haL hmL third hLK hm haK hab u hy
    · exact SL_mul_torusK hmL (h_mem_torusK hab haK hbK u) hy

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.SL_mul_h

theorem SL_mul_gen {g : SteinbergGroup I R} (hg : g ∈ torusSet I R (insert L K))
    {y : SteinbergGroup I R} (hy : y ∈ torusSL R K hmL) : g * y ∈ torusSL R K hmL := by
  rcases hg with ⟨a, b, hab, u, ⟨ha, hb⟩, rfl⟩ | hs
  · exact SL_mul_h hmL third hLK hm hab ha hb u hy
  · exact SL_mul_torusK hmL (symGroup_le_torusK K (Subgroup.subset_closure hs)) hy

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.SL_mul_gen

theorem SL_mul_gen_inv {g : SteinbergGroup I R} (hg : g ∈ torusSet I R (insert L K))
    {y : SteinbergGroup I R} (hy : y ∈ torusSL R K hmL) : g⁻¹ * y ∈ torusSL R K hmL := by
  rcases hg with ⟨a, b, hab, u, ⟨ha, hb⟩, rfl⟩ | hs
  · rw [h_inv_eq, mul_assoc]
    exact SL_mul_h hmL third hLK hm hab ha hb u⁻¹
      (SL_mul_torusK hmL (symGroup_le_torusK K (csym_mem_symGroup _ _ _)) hy)
  · exact SL_mul_torusK hmL (Subgroup.inv_mem _
      (symGroup_le_torusK K (Subgroup.subset_closure hs))) hy

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.SL_mul_gen_inv

/-- `T_{K ∪ {L}} ⊆ T_K · h_mL(Rˣ)`. -/
theorem torusK_insert_subset {t : SteinbergGroup I R} (ht : t ∈ torusK I R (insert L K)) :
    t ∈ torusSL R K hmL := by
  rw [torusK] at ht
  induction ht using Subgroup.closure_induction_left with
  | one => exact ⟨1, Subgroup.one_mem _, 1, by rw [h_one, mul_one]⟩
  | mul_left x hx y _ hy => exact SL_mul_gen hmL third hLK hm hx hy
  | inv_mul_cancel x hx y _ hy => exact SL_mul_gen_inv hmL third hLK hm hx hy

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.torusK_insert_subset

end Absorb

/-- **The torus meets `K₂` only in symbols.** An element of `T_K` acting trivially on `R^I`
lies in the subgroup generated by the symbols. -/
theorem torus_faith (third : ThirdIndex I) (K : Finset I) :
    ∀ t ∈ torusK I R K, (∀ y : I → R, act t y = y) → t ∈ symGroup I R := by
  induction K using Finset.induction_on with
  | empty =>
    intro t ht _
    refine (Subgroup.closure_le _).mpr ?_ ht
    rintro _ (⟨a, b, hab, u, ⟨ha, -⟩, rfl⟩ | hs)
    · exact absurd ha (Finset.notMem_empty a)
    · exact Subgroup.subset_closure hs
  | insert L K hLK ih =>
    intro t ht hfix
    rcases K.eq_empty_or_nonempty with hK | ⟨m, hm⟩
    · subst hK
      have key : ∀ y : I, y ∈ insert L (∅ : Finset I) → y = L := fun y hy =>
        (Finset.mem_insert.mp hy).resolve_right (Finset.notMem_empty y)
      refine (Subgroup.closure_le _).mpr ?_ ht
      rintro _ (⟨a, b, hab, u, ⟨ha, hb⟩, rfl⟩ | hs)
      · exact absurd ((key a ha).trans (key b hb).symm) hab
      · exact Subgroup.subset_closure hs
    · have hmL : m ≠ L := fun e => hLK (by rw [← e]; exact hm)
      obtain ⟨t', ht', c, rfl⟩ := torusK_insert_subset hmL third hLK hm ht
      have hc : c = 1 := by
        have e := congrFun (hfix (unitVec L)) L
        rw [act_mul, act_hmL_unitVec hmL c, act_smul', torusK_fix_L hLK ht', Pi.smul_apply,
          smul_eq_mul, unitVec_apply, if_pos rfl, mul_one] at e
        exact inv_eq_one.mp (Units.val_eq_one.mp e)
      subst hc
      rw [h_one, mul_one] at hfix ⊢
      exact ih t' ht' hfix

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.torus_faith

end GroupApproximation.BooneHigmanLinear.RelGen
