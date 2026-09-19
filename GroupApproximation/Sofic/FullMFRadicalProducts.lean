import GroupApproximation.Sofic.FullMFRadicalReflection

/-!
# Products of intrinsic MF cores

The intrinsic full-MF core is computed coordinatewise on a direct product.
Consequently both intrinsically full groups and core-free groups are closed
under binary products, and the core-free reflection preserves them.
-/

namespace GroupApproximation

universe u v

variable {G : Type u} [Group G] {H : Type v} [Group H]

/-- Membership in the intrinsic core of a direct product is coordinatewise. -/
theorem mem_fullMFRadicalCore_prod_iff (x : G × H) :
    x ∈ fullMFRadicalCore (G × H) ↔
      x.1 ∈ fullMFRadicalCore G ∧ x.2 ∈ fullMFRadicalCore H := by
  let π₁ : G × H →* G :=
    { toFun := Prod.fst
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let π₂ : G × H →* H :=
    { toFun := Prod.snd
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let ι₁ : G →* G × H :=
    { toFun := fun g => (g, 1)
      map_one' := by simp
      map_mul' := by simp }
  let ι₂ : H →* G × H :=
    { toFun := fun h => (1, h)
      map_one' := by simp
      map_mul' := by simp }
  constructor
  · intro hx
    constructor
    · exact map_fullMFRadicalCore_le π₁
        (Subgroup.mem_map_of_mem π₁ hx)
    · exact map_fullMFRadicalCore_le π₂
        (Subgroup.mem_map_of_mem π₂ hx)
  · rintro ⟨hx, hy⟩
    have hleft : (x.1, 1) ∈ fullMFRadicalCore (G × H) :=
      map_fullMFRadicalCore_le ι₁
        (Subgroup.mem_map_of_mem ι₁ hx)
    have hright : (1, x.2) ∈ fullMFRadicalCore (G × H) :=
      map_fullMFRadicalCore_le ι₂
        (Subgroup.mem_map_of_mem ι₂ hy)
    simpa using
      (fullMFRadicalCore (G × H)).mul_mem hleft hright

/-- A direct product has full intrinsic core exactly when both factors do. -/
theorem fullMFRadicalCore_prod_eq_top_iff :
    fullMFRadicalCore (G × H) = ⊤ ↔
      fullMFRadicalCore G = ⊤ ∧ fullMFRadicalCore H = ⊤ := by
  constructor
  · intro hprod
    constructor
    · apply top_unique
      intro g hg
      exact (mem_fullMFRadicalCore_prod_iff (G := G) (H := H) (g, 1)).mp
        (by rw [hprod]; exact Subgroup.mem_top _)
        |>.1
    · apply top_unique
      intro h hh
      exact (mem_fullMFRadicalCore_prod_iff (G := G) (H := H) (1, h)).mp
        (by rw [hprod]; exact Subgroup.mem_top _)
        |>.2
  · rintro ⟨hG, hH⟩
    apply top_unique
    intro x hx
    apply (mem_fullMFRadicalCore_prod_iff (G := G) (H := H) x).mpr
    constructor
    · rw [hG]
      exact Subgroup.mem_top _
    · rw [hH]
      exact Subgroup.mem_top _

/-- A direct product is core-free exactly when both factors are core-free. -/
theorem fullMFRadicalCore_prod_eq_bot_iff :
    fullMFRadicalCore (G × H) = ⊥ ↔
      fullMFRadicalCore G = ⊥ ∧ fullMFRadicalCore H = ⊥ := by
  constructor
  · intro hprod
    constructor
    · apply le_antisymm _ bot_le
      intro g hg
      rw [Subgroup.mem_bot]
      have hpair : (g, 1) ∈ fullMFRadicalCore (G × H) :=
        (mem_fullMFRadicalCore_prod_iff (G := G) (H := H) (g, 1)).mpr
          ⟨hg, (fullMFRadicalCore H).one_mem⟩
      rw [hprod] at hpair
      exact congrArg Prod.fst (Subgroup.mem_bot.mp hpair)
    · apply le_antisymm _ bot_le
      intro h hh
      rw [Subgroup.mem_bot]
      have hpair : (1, h) ∈ fullMFRadicalCore (G × H) :=
        (mem_fullMFRadicalCore_prod_iff (G := G) (H := H) (1, h)).mpr
          ⟨(fullMFRadicalCore G).one_mem, hh⟩
      rw [hprod] at hpair
      exact congrArg Prod.snd (Subgroup.mem_bot.mp hpair)
  · rintro ⟨hG, hH⟩
    apply le_antisymm _ bot_le
    intro x hx
    rw [Subgroup.mem_bot]
    have hxy :=
      (mem_fullMFRadicalCore_prod_iff (G := G) (H := H) x).mp hx
    rw [hG] at hxy
    rw [hH] at hxy
    exact Prod.ext (Subgroup.mem_bot.mp hxy.1) (Subgroup.mem_bot.mp hxy.2)

/-- Direct products have full genuine-corona MF residual exactly when both
factors do. -/
theorem actualCoronaMFResidual_prod_eq_top_iff :
    actualCoronaMFResidual (G × H) = ⊤ ↔
      actualCoronaMFResidual G = ⊤ ∧
        actualCoronaMFResidual H = ⊤ := by
  constructor
  · intro hprod
    have hcore :=
      (fullMFRadicalCore_eq_top_iff (G := G × H)).mpr hprod
    have hfactor :=
      (fullMFRadicalCore_prod_eq_top_iff (G := G) (H := H)).mp hcore
    exact ⟨(fullMFRadicalCore_eq_top_iff (G := G)).mp hfactor.1,
      (fullMFRadicalCore_eq_top_iff (G := H)).mp hfactor.2⟩
  · rintro ⟨hG, hH⟩
    apply (fullMFRadicalCore_eq_top_iff (G := G × H)).mp
    apply (fullMFRadicalCore_prod_eq_top_iff (G := G) (H := H)).mpr
    exact ⟨(fullMFRadicalCore_eq_top_iff (G := G)).mpr hG,
      (fullMFRadicalCore_eq_top_iff (G := H)).mpr hH⟩

end GroupApproximation
