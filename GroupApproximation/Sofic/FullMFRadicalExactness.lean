import GroupApproximation.Sofic.FullMFRadicalCore

/-!
# Exactness and orthogonality for the intrinsic MF core

The intrinsic full-MF core is not merely functorial.  A surjection carries it
onto the target core whenever the kernel is intrinsically full.  Consequently
quotients by intrinsically full normal subgroups preserve the core exactly.

The full-core groups and the core-free groups form the two sides of a
canonical decomposition: every map from the former to the latter is trivial,
and this orthogonality characterizes full-core groups.
-/

namespace GroupApproximation

universe u v

variable {G : Type u} [Group G]

/-- A surjection with intrinsically full kernel carries the intrinsic core
onto the intrinsic core of the target. -/
theorem map_fullMFRadicalCore_eq_of_surjective_of_kernel_eq_top
    {H : Type v} [Group H] (f : G →* H) (hf : Function.Surjective f)
    (hker : actualCoronaMFResidual f.ker = ⊤) :
    (fullMFRadicalCore G).map f = fullMFRadicalCore H := by
  apply le_antisymm (map_fullMFRadicalCore_le f)
  unfold fullMFRadicalCore
  apply iSup_le
  intro K
  let P : Subgroup G := K.1.comap f
  have hkerP : f.ker ≤ P := by
    intro x hx
    change f x ∈ K.1
    rw [MonoidHom.mem_ker.mp hx]
    exact K.1.one_mem
  let φ : P →* P.map f := KazhdanCompressionCore.subgroupMapHom P f
  have hφ : Function.Surjective φ :=
    KazhdanCompressionCore.subgroupMapHom_surjective P f
  let j : f.ker →* φ.ker :=
    { toFun := fun x ↦ ⟨⟨x, hkerP x.property⟩, by
        rw [MonoidHom.mem_ker]
        apply Subtype.ext
        change f (x : G) = 1
        exact x.property⟩
      map_one' := by ext; rfl
      map_mul' := by intro x y; ext; rfl }
  have hj : Function.Surjective j := by
    rintro ⟨⟨x, hxP⟩, hxker⟩
    have hfx : f x = 1 := by
      exact congrArg Subtype.val (MonoidHom.mem_ker.mp hxker)
    refine ⟨⟨x, hfx⟩, ?_⟩
    ext
    rfl
  have hφker : actualCoronaMFResidual φ.ker = ⊤ :=
    actualCoronaMFResidual_eq_top_of_surjective j hj hker
  have hPK : P.map f = K.1 := by
    dsimp [P]
    exact Subgroup.map_comap_eq_self_of_surjective hf K.1
  have htarget : actualCoronaMFResidual (P.map f) = ⊤ := by
    rw [hPK]
    exact K.2
  have hP : actualCoronaMFResidual P = ⊤ :=
    actualCoronaMFResidual_eq_top_of_surjective_kernel φ hφ hφker htarget
  have hPC : P ≤ fullMFRadicalCore G := le_fullMFRadicalCore P hP
  intro y hy
  obtain ⟨x, rfl⟩ := hf y
  exact Subgroup.mem_map_of_mem f (hPC hy)

/-- Quotienting by an intrinsically full normal subgroup computes the target
core as the image of the source core. -/
theorem map_fullMFRadicalCore_quotient_eq
    (N : Subgroup G) [N.Normal]
    (hN : actualCoronaMFResidual N = ⊤) :
    (fullMFRadicalCore G).map (QuotientGroup.mk' N) =
      fullMFRadicalCore (G ⧸ N) := by
  apply map_fullMFRadicalCore_eq_of_surjective_of_kernel_eq_top
    (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  rw [QuotientGroup.ker_mk']
  exact hN

/-- A subgroup of a core-free group is core-free. -/
theorem fullMFRadicalCore_subgroup_eq_bot_of_eq_bot
    (K : Subgroup G) (hG : fullMFRadicalCore G = ⊥) :
    fullMFRadicalCore K = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  have hmap : (x : G) ∈ fullMFRadicalCore G :=
    map_fullMFRadicalCore_le K.subtype
      (Subgroup.mem_map_of_mem K.subtype hx)
  rw [hG] at hmap
  exact Subgroup.mem_bot.mp hmap

/-- Full-core groups are left-orthogonal to core-free groups. -/
theorem hom_eq_one_of_source_core_eq_top_of_target_core_eq_bot
    {H : Type v} [Group H] (f : G →* H)
    (hG : fullMFRadicalCore G = ⊤)
    (hH : fullMFRadicalCore H = ⊥) :
    f = 1 :=
  hom_eq_one_of_fullMFRadicalCore_eq_top_of_target_eq_bot f hG hH

/-- Orthogonality to every core-free group characterizes full-core groups. -/
theorem fullMFRadicalCore_eq_top_iff_maps_to_coreFree_eq_one :
    fullMFRadicalCore G = ⊤ ↔
      ∀ {H : Type u} [Group H] (f : G →* H),
        fullMFRadicalCore H = ⊥ → f = 1 := by
  constructor
  · intro hG H _ f hH
    exact hom_eq_one_of_source_core_eq_top_of_target_core_eq_bot f hG hH
  · intro horth
    letI : (fullMFRadicalCore G).Normal := fullMFRadicalCore_normal
    let q : G →* G ⧸ fullMFRadicalCore G :=
      QuotientGroup.mk' (fullMFRadicalCore G)
    have hq : q = 1 :=
      horth q fullMFRadicalCore_quotient_eq_bot
    apply top_unique
    intro x hx
    apply (QuotientGroup.eq_one_iff x).mp
    change q x = 1
    rw [hq]
    rfl

end GroupApproximation
