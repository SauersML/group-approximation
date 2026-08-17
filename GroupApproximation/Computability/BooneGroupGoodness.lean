import GroupApproximation.Computability.BooneGroupTower
import GroupApproximation.Computability.BooneGroupMachineIndex

/-!
# S5b: the halting subgroup is good at every quadruple

`BooneGroupMachineIndex` (S5a) computes both sides of a quadruple as the two
images of **one and the same** parameter set:

* `twSub_halting_inf_Gsub_src` --- `T_M ⊓ G_{ab}^{MM}` is `twSub` of the image
  of `haltParams` under `embIdx a b M M`;
* `twSub_halting_inf_Gsub_right` --- `T_M ⊓ G_{c0}^{M²,1}` is `twSub` of the
  image of the *same* `haltParams` under `embIdx c 0 M² 1`.

`twSub_map_emb` says `emb` carries `twSub` of a set to `twSub` of its image.
Composing the three gives Simpson's Definition 2 for `T_M` --- goodness --- with
no computation left to do, and `liftedSubgroup_inf_range` (S4) then applies.
-/

namespace GroupApproximation
namespace BooneGroup

open Base MachineIndex

variable (mm : ModularMachine)

/-- **Goodness of the halting subgroup at a right-moving quadruple.**  This is
Simpson's Definition 2 for `T_M`, and it is exactly S5a's two computations read
through `emb`. -/
theorem good_twSub_halting_right {a b c : ℕ} (ha : a < mm.size) (hb : b < mm.size)
    (hq : mm.quad a b = some (c, true)) (hM : (mm.size : ℤ) ≠ 0) :
    Good (twSub mm.haltingSetZ)
      (quadEquiv (a : ℤ) (b : ℤ) (c : ℤ) (mm.size : ℤ) hM) := by
  have hM2 : ((mm.size : ℤ)) ^ 2 ≠ 0 := pow_ne_zero 2 hM
  have he₁ : Function.Injective (emb (a : ℤ) (b : ℤ) (mm.size : ℤ) (mm.size : ℤ)) :=
    emb_injective hM hM
  have he₂ : Function.Injective (emb (c : ℤ) 0 ((mm.size : ℤ) ^ 2) 1) :=
    emb_injective hM2 one_ne_zero
  constructor
  · rintro x hx
    obtain ⟨y, hy⟩ := x.2
    have hsym : (MonoidHom.ofInjective he₁).symm x = y := by
      apply (MonoidHom.ofInjective he₁).injective
      rw [MulEquiv.apply_symm_apply]
      exact Subtype.ext hy.symm
    have h1 : emb (a : ℤ) (b : ℤ) (mm.size : ℤ) (mm.size : ℤ) y ∈
        twSub mm.haltingSetZ ⊓ Gsub (a : ℤ) (b : ℤ) (mm.size : ℤ) (mm.size : ℤ) := by
      rw [hy]
      exact ⟨hx, x.2⟩
    rw [twSub_halting_inf_Gsub_src mm a b] at h1
    have h2 : y ∈ twSub (haltParams mm a b) :=
      (emb_mem_twSub_iff hM hM _ y).mp h1
    have h3 : emb (c : ℤ) 0 ((mm.size : ℤ) ^ 2) 1 y ∈
        twSub ((embIdx (c : ℤ) 0 ((mm.size : ℤ) ^ 2) 1) '' haltParams mm a b) :=
      (emb_mem_twSub_iff hM2 one_ne_zero _ y).mpr h2
    rw [← twSub_halting_inf_Gsub_right mm ha hb hq] at h3
    have h4 : ((quadEquiv (a : ℤ) (b : ℤ) (c : ℤ) (mm.size : ℤ) hM x : _) : BaseGroup)
        = emb (c : ℤ) 0 ((mm.size : ℤ) ^ 2) 1
            ((MonoidHom.ofInjective he₁).symm x) := rfl
    rw [h4, hsym]
    exact h3.1
  · rintro z hz
    obtain ⟨y, hy⟩ := z.2
    have hsym : (MonoidHom.ofInjective he₂).symm z = y := by
      apply (MonoidHom.ofInjective he₂).injective
      rw [MulEquiv.apply_symm_apply]
      exact Subtype.ext hy.symm
    have h1 : emb (c : ℤ) 0 ((mm.size : ℤ) ^ 2) 1 y ∈
        twSub mm.haltingSetZ ⊓ Gsub (c : ℤ) 0 ((mm.size : ℤ) ^ 2) 1 := by
      rw [hy]
      exact ⟨hz, z.2⟩
    rw [twSub_halting_inf_Gsub_right mm ha hb hq] at h1
    have h2 : y ∈ twSub (haltParams mm a b) :=
      (emb_mem_twSub_iff hM2 one_ne_zero _ y).mp h1
    have h3 : emb (a : ℤ) (b : ℤ) (mm.size : ℤ) (mm.size : ℤ) y ∈
        twSub ((embIdx (a : ℤ) (b : ℤ) (mm.size : ℤ) (mm.size : ℤ))
          '' haltParams mm a b) :=
      (emb_mem_twSub_iff hM hM _ y).mpr h2
    rw [← twSub_halting_inf_Gsub_src mm a b] at h3
    have h4 : (((quadEquiv (a : ℤ) (b : ℤ) (c : ℤ) (mm.size : ℤ) hM).symm z : _)
        : BaseGroup) = emb (a : ℤ) (b : ℤ) (mm.size : ℤ) (mm.size : ℤ)
            ((MonoidHom.ofInjective he₂).symm z) := rfl
    rw [h4, hsym]
    exact h3.1

/-- **Goodness of the halting subgroup at a left-moving quadruple.**  This is
Simpson's Definition 2 for `T_M`, and it is exactly S5a's two computations read
through `emb`. -/
theorem good_twSub_halting_left {a b c : ℕ} (ha : a < mm.size) (hb : b < mm.size)
    (hq : mm.quad a b = some (c, false)) (hM : (mm.size : ℤ) ≠ 0) :
    Good (twSub mm.haltingSetZ)
      (quadEquivLeft (a : ℤ) (b : ℤ) (c : ℤ) (mm.size : ℤ) hM) := by
  have hM2 : ((mm.size : ℤ)) ^ 2 ≠ 0 := pow_ne_zero 2 hM
  have he₁ : Function.Injective (emb (a : ℤ) (b : ℤ) (mm.size : ℤ) (mm.size : ℤ)) :=
    emb_injective hM hM
  have he₂ : Function.Injective (emb 0 (c : ℤ) 1 ((mm.size : ℤ) ^ 2)) :=
    emb_injective one_ne_zero hM2
  constructor
  · rintro x hx
    obtain ⟨y, hy⟩ := x.2
    have hsym : (MonoidHom.ofInjective he₁).symm x = y := by
      apply (MonoidHom.ofInjective he₁).injective
      rw [MulEquiv.apply_symm_apply]
      exact Subtype.ext hy.symm
    have h1 : emb (a : ℤ) (b : ℤ) (mm.size : ℤ) (mm.size : ℤ) y ∈
        twSub mm.haltingSetZ ⊓ Gsub (a : ℤ) (b : ℤ) (mm.size : ℤ) (mm.size : ℤ) := by
      rw [hy]
      exact ⟨hx, x.2⟩
    rw [twSub_halting_inf_Gsub_src mm a b] at h1
    have h2 : y ∈ twSub (haltParams mm a b) :=
      (emb_mem_twSub_iff hM hM _ y).mp h1
    have h3 : emb 0 (c : ℤ) 1 ((mm.size : ℤ) ^ 2) y ∈
        twSub ((embIdx 0 (c : ℤ) 1 ((mm.size : ℤ) ^ 2)) '' haltParams mm a b) :=
      (emb_mem_twSub_iff one_ne_zero hM2 _ y).mpr h2
    rw [← twSub_halting_inf_Gsub_left mm ha hb hq] at h3
    have h4 : ((quadEquivLeft (a : ℤ) (b : ℤ) (c : ℤ) (mm.size : ℤ) hM x : _) : BaseGroup)
        = emb 0 (c : ℤ) 1 ((mm.size : ℤ) ^ 2)
            ((MonoidHom.ofInjective he₁).symm x) := rfl
    rw [h4, hsym]
    exact h3.1
  · rintro z hz
    obtain ⟨y, hy⟩ := z.2
    have hsym : (MonoidHom.ofInjective he₂).symm z = y := by
      apply (MonoidHom.ofInjective he₂).injective
      rw [MulEquiv.apply_symm_apply]
      exact Subtype.ext hy.symm
    have h1 : emb 0 (c : ℤ) 1 ((mm.size : ℤ) ^ 2) y ∈
        twSub mm.haltingSetZ ⊓ Gsub 0 (c : ℤ) 1 ((mm.size : ℤ) ^ 2) := by
      rw [hy]
      exact ⟨hz, z.2⟩
    rw [twSub_halting_inf_Gsub_left mm ha hb hq] at h1
    have h2 : y ∈ twSub (haltParams mm a b) :=
      (emb_mem_twSub_iff one_ne_zero hM2 _ y).mp h1
    have h3 : emb (a : ℤ) (b : ℤ) (mm.size : ℤ) (mm.size : ℤ) y ∈
        twSub ((embIdx (a : ℤ) (b : ℤ) (mm.size : ℤ) (mm.size : ℤ))
          '' haltParams mm a b) :=
      (emb_mem_twSub_iff hM hM _ y).mpr h2
    rw [← twSub_halting_inf_Gsub_src mm a b] at h3
    have h4 : (((quadEquivLeft (a : ℤ) (b : ℤ) (c : ℤ) (mm.size : ℤ) hM).symm z : _)
        : BaseGroup) = emb (a : ℤ) (b : ℤ) (mm.size : ℤ) (mm.size : ℤ)
            ((MonoidHom.ofInjective he₂).symm z) := rfl
    rw [h4, hsym]
    exact h3.1

/-- **S5b at a quadruple.**  Feeding goodness into S4: inside the extension that
adjoins the stable letter for this quadruple, the elements of `T_M'` lying in the
base group are exactly those of `T_M`.

This is the statement Simpson's Lemma 7 (S6) consumes. -/
theorem twSub_halting_liftedSubgroup_inf_right {a b c : ℕ} (ha : a < mm.size)
    (hb : b < mm.size) (hq : mm.quad a b = some (c, true))
    (hM : (mm.size : ℤ) ≠ 0) :
    liftedSubgroup (quadEquiv (a : ℤ) (b : ℤ) (c : ℤ) (mm.size : ℤ) hM)
        (twSub mm.haltingSetZ) ⊓
      (HNNExtension.of :
        BaseGroup →* HNNExtension BaseGroup
          (Gsub (a : ℤ) (b : ℤ) (mm.size : ℤ) (mm.size : ℤ))
          (Gsub (c : ℤ) 0 ((mm.size : ℤ) ^ 2) 1)
          (quadEquiv (a : ℤ) (b : ℤ) (c : ℤ) (mm.size : ℤ) hM)).range
      = (twSub mm.haltingSetZ).map HNNExtension.of :=
  liftedSubgroup_inf_range _ (good_twSub_halting_right mm ha hb hq hM)

/-- **S5b at a left-moving quadruple.** -/
theorem twSub_halting_liftedSubgroup_inf_left {a b c : ℕ} (ha : a < mm.size)
    (hb : b < mm.size) (hq : mm.quad a b = some (c, false))
    (hM : (mm.size : ℤ) ≠ 0) :
    liftedSubgroup (quadEquivLeft (a : ℤ) (b : ℤ) (c : ℤ) (mm.size : ℤ) hM)
        (twSub mm.haltingSetZ) ⊓
      (HNNExtension.of :
        BaseGroup →* HNNExtension BaseGroup
          (Gsub (a : ℤ) (b : ℤ) (mm.size : ℤ) (mm.size : ℤ))
          (Gsub 0 (c : ℤ) 1 ((mm.size : ℤ) ^ 2))
          (quadEquivLeft (a : ℤ) (b : ℤ) (c : ℤ) (mm.size : ℤ) hM)).range
      = (twSub mm.haltingSetZ).map HNNExtension.of :=
  liftedSubgroup_inf_range _ (good_twSub_halting_left mm ha hb hq hM)

end BooneGroup
end GroupApproximation
