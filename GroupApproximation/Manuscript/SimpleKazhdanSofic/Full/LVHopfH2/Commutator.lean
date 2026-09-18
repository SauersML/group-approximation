import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVHopfH2.Chains

/-!
# Hopf formula versus `groupHomology.H2`: cycles land in the multiplier (lane LVHopfH2)

`simple_kazhdan_sofic_group.tex`, `sec:questions`, l.733-735 (Hopf formula; Brown II.5 Thm 5.3).

* `mem_hopfMultiplier_iff_ext`: `hopfMultiplier f = K ∩ [E,E]` inside `E = F ⧸ [F,R]`.
* `hopfExtAb_comp_phi`: `ab ∘ Φ = S ∘ ∂₂`, where `S g = [σ g]` in the abelianization of `E`.
* `hopfChainPhi_mem_commutator`: `Φ` maps 2-cycles into `[E,E]`.
-/

namespace GroupApproximation.Full.LVHopf

section Commutator

variable {G : Type} [Group G] {α : Type} {f : FreeGroup α →* G}

/-- The Hopf multiplier is `K ∩ [E,E]` in `E = F ⧸ [F,R]` (Hopf formula, l.733-735). -/
theorem mem_hopfMultiplier_iff_ext (z : HopfExt f) :
    z ∈ hopfMultiplier f ↔ z ∈ (hopfExtProj f).ker ∧ z ∈ commutator (HopfExt f) := by
  constructor
  · intro hz
    obtain ⟨x, hx, rfl⟩ := (mem_hopfMultiplier f).mp hz
    have hxR : x ∈ f.ker := (Subgroup.mem_inf.mp hx).1
    have hxC : x ∈ commutator (FreeGroup α) := (Subgroup.mem_inf.mp hx).2
    refine ⟨MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp hxR), ?_⟩
    exact map_commutator_le (QuotientGroup.mk' ⁅(⊤ : Subgroup (FreeGroup α)), f.ker⁆)
      (Subgroup.mem_map_of_mem (QuotientGroup.mk' ⁅(⊤ : Subgroup (FreeGroup α)), f.ker⁆) hxC)
  · rintro ⟨hK, hC⟩
    have hC' : z ∈ (commutator (FreeGroup α)).map
        (QuotientGroup.mk' ⁅(⊤ : Subgroup (FreeGroup α)), f.ker⁆) := by
      rw [map_commutator_of_surjective
        (QuotientGroup.mk' ⁅(⊤ : Subgroup (FreeGroup α)), f.ker⁆)
        (QuotientGroup.mk'_surjective ⁅(⊤ : Subgroup (FreeGroup α)), f.ker⁆)]
      exact hC
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hC'
    have hyR : y ∈ f.ker := MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp hK)
    exact (mem_hopfMultiplier f).mpr ⟨y, Subgroup.mem_inf.mpr ⟨hyR, hy⟩, rfl⟩

variable (f) in
/-- `K → E → Eᵃᵇ`, additively. -/
noncomputable def hopfExtAb : Additive (HopfExtK f) →+ Additive (Abelianization (HopfExt f)) :=
  MonoidHom.toAdditive (Abelianization.of.comp (hopfExtProj f).ker.subtype)

/-- `S : ℤ[G] → Eᵃᵇ`, `g ↦ [σ g]`. -/
noncomputable def hopfExtS (hf : Function.Surjective f) :
    (G →₀ ℤ) →+ Additive (Abelianization (HopfExt f)) :=
  Finsupp.liftAddHom fun g =>
    zmultiplesHom (Additive (Abelianization (HopfExt f)))
      (Additive.ofMul (Abelianization.of (hopfExtSec hf g)))

theorem hopfExtS_single_one (hf : Function.Surjective f) (g : G) :
    hopfExtS hf (Finsupp.single g 1) = Additive.ofMul (Abelianization.of (hopfExtSec hf g)) := by
  simp only [hopfExtS, Finsupp.liftAddHom_apply_single, zmultiplesHom_apply, one_zsmul]

/-- `ab ∘ Φ = S ∘ ∂₂`. -/
theorem hopfExtAb_comp_phi (hf : Function.Surjective f) :
    (hopfExtAb f).comp (hopfChainPhi hf) = (hopfExtS hf).comp hopfChainD := by
  apply hopfChain_addHom_ext
  rintro ⟨g, h⟩
  have hL : hopfExtAb f (hopfChainPhi hf (Finsupp.single (g, h) 1)) =
      Additive.ofMul (Abelianization.of (hopfExtSec hf g)) +
        Additive.ofMul (Abelianization.of (hopfExtSec hf h)) +
          -Additive.ofMul (Abelianization.of (hopfExtSec hf (g * h))) := by
    rw [hopfChainPhi_single_one hf g h]
    have e : Abelianization.of (hopfExtRc hf g h) =
        Abelianization.of (hopfExtSec hf g) * Abelianization.of (hopfExtSec hf h) *
          (Abelianization.of (hopfExtSec hf (g * h)))⁻¹ := by
      rw [hopfExtRc, map_mul, map_mul, map_inv]
    exact congrArg Additive.ofMul e
  have hR : hopfExtS hf (hopfChainD (Finsupp.single (g, h) 1)) =
      Additive.ofMul (Abelianization.of (hopfExtSec hf h)) -
        Additive.ofMul (Abelianization.of (hopfExtSec hf (g * h))) +
          Additive.ofMul (Abelianization.of (hopfExtSec hf g)) := by
    rw [hopfChainD_single, map_add, map_sub, hopfExtS_single_one hf h,
      hopfExtS_single_one hf (g * h), hopfExtS_single_one hf g]
  rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, hL, hR]
  abel

/-- `Φ` maps 2-cycles into `[E,E]` (Hopf formula, l.733-735). -/
theorem hopfChainPhi_mem_commutator (hf : Function.Surjective f) {c : G × G →₀ ℤ}
    (hc : hopfChainD c = 0) :
    ((Additive.toMul (hopfChainPhi hf c) : HopfExtK f) : HopfExt f) ∈
      commutator (HopfExt f) := by
  have h := DFunLike.congr_fun (hopfExtAb_comp_phi hf) c
  rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, hc, map_zero] at h
  exact (abelianization_of_eq_one_iff
    ((Additive.toMul (hopfChainPhi hf c) : HopfExtK f) : HopfExt f)).mp h

/-- `Φ` maps 2-cycles into the Hopf multiplier. -/
theorem hopfChainPhi_mem_hopfMultiplier (hf : Function.Surjective f) {c : G × G →₀ ℤ}
    (hc : hopfChainD c = 0) :
    ((Additive.toMul (hopfChainPhi hf c) : HopfExtK f) : HopfExt f) ∈ hopfMultiplier f :=
  (mem_hopfMultiplier_iff_ext _).mpr
    ⟨(Additive.toMul (hopfChainPhi hf c)).2, hopfChainPhi_mem_commutator hf hc⟩

end Commutator

end GroupApproximation.Full.LVHopf
