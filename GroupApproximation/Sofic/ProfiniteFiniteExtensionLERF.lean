import GroupApproximation.Algebra.SchreierGenerators
import GroupApproximation.Sofic.ProfiniteFiniteIndexPromotion

/-!
# LERF promotion through a finite normal extension

If a normal finite-index subgroup is LERF, then the ambient group is LERF.
The proof uses the quotient by the normal subgroup to put an offending
element in the kernel, and finite-index promotion for the trace of the given
finitely generated subgroup.
-/

namespace GroupApproximation

noncomputable section

variable {G : Type} [Group G]

/-- The two intrinsic versions of `H ∩ K` differ only in which subgroup
membership is bundled first. -/
def subgroupComapSwap (H K : Subgroup G) :
    H.comap K.subtype ≃* K.subgroupOf H where
  toFun x := ⟨⟨x.1.1, x.2⟩, x.1.2⟩
  invFun x := ⟨⟨x.1.1, x.2⟩, x.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- **A finite extension of a LERF group is LERF.**  The normality assumption
is harmless in applications: an arbitrary finite-index subgroup may first be
replaced by its normal core. -/
theorem profiniteClosure_eq_of_normal_finiteIndex_lerf
    (K : Subgroup G) [K.Normal] [K.FiniteIndex]
    (hK : ∀ L : Subgroup K, L.FG → profiniteClosure L = L)
    (H : Subgroup G) (hH : H.FG) :
    profiniteClosure H = H := by
  let L : Subgroup K := H.comap K.subtype
  haveI : Group.FG H := (Group.fg_iff_subgroup_fg H).mpr hH
  haveI : (K.subgroupOf H).FiniteIndex :=
    Subgroup.instFiniteIndex_subgroupOf K H
  haveI : Group.FG (K.subgroupOf H) :=
    FiniteIndex.group_fg_of_finiteIndex (K.subgroupOf H)
  haveI : Group.FG L :=
    Group.fg_of_surjective
      (f := (subgroupComapSwap H K).symm.toMonoidHom)
      (subgroupComapSwap H K).symm.surjective
  have hLfg : L.FG := (Group.fg_iff_subgroup_fg L).mp inferInstance
  have hLclosed : profiniteClosure L = L := hK L hLfg
  have htraceClosed :
      profiniteClosure (L.map K.subtype) = L.map K.subtype :=
    profiniteClosure_map_subtype_eq_of_closed K L hLclosed
  have htrace : L.map K.subtype = H ⊓ K := by
    ext x
    constructor
    · rintro ⟨k, hkH, hkx⟩
      have hkx' : (k : G) = x := hkx
      exact ⟨hkx' ▸ hkH, hkx' ▸ k.2⟩
    · rintro ⟨hxH, hxK⟩
      exact ⟨⟨x, hxK⟩, hxH, rfl⟩
  rw [htrace] at htraceClosed
  apply le_antisymm
  · intro x hx
    let p : G →* G ⧸ K := QuotientGroup.mk' K
    have hxbase : p x ∈ H.map p := hx (G ⧸ K) p
    obtain ⟨c, hc, hcx⟩ := Subgroup.mem_map.mp hxbase
    let y : G := c⁻¹ * x
    have hyK : y ∈ K := by
      have hpy : p y = 1 := by
        dsimp [y]
        rw [map_mul, map_inv, hcx, inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff y).mp hpy
    have hyClosure : y ∈ profiniteClosure (H ⊓ K) := by
      intro Q _ _ q
      let test : G →* (G ⧸ K) × Q := p.prod q
      have htest : test x ∈ H.map test := hx ((G ⧸ K) × Q) test
      obtain ⟨h, hh, hhx⟩ := Subgroup.mem_map.mp htest
      have hp := congrArg Prod.fst hhx
      have hq := congrArg Prod.snd hhx
      change p h = p x at hp
      change q h = q x at hq
      refine ⟨c⁻¹ * h, ?_, ?_⟩
      · constructor
        · exact H.mul_mem (H.inv_mem hc) hh
        · have hpk : p (c⁻¹ * h) = 1 := by
            rw [map_mul, map_inv, hp, hcx, inv_mul_cancel]
          exact (QuotientGroup.eq_one_iff (c⁻¹ * h)).mp hpk
      · calc
          q (c⁻¹ * h) = (q c)⁻¹ * q h := by rw [map_mul, map_inv]
          _ = (q c)⁻¹ * q x := by rw [hq]
          _ = q (c⁻¹ * x) := by rw [map_mul, map_inv]
          _ = q y := by rfl
    rw [htraceClosed] at hyClosure
    have hxy : x = c * y := by
      dsimp [y]
      group
    rw [hxy]
    exact H.mul_mem hc hyClosure.1
  · exact le_profiniteClosure H

end

end GroupApproximation
