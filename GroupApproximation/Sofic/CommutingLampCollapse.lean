import GroupApproximation.Sofic.ProjectionCompressionCollapse
import GroupApproximation.Sofic.MarkedCompressionGroup
import GroupApproximation.Sofic.LiteralBaseAffineQuotient
import GroupApproximation.Sofic.LiteralBaseP13PropertyTBridge
import GroupApproximation.Sofic.LiteralNonMFLinearWitness
import GroupApproximation.Algebra.CountableInstances

/-!
# The sign-free commuting-lamp quotient is not MF

Quotienting the marked-compression ambient group by its central Clifford
sign makes all lamps commute.  The moved root lamp is then literally an
involutive compression witness: it is an involution, the compressed base
copy fixes its site, and its orbit commutes because the sign is gone.
The kernel-checked involutive collapse therefore places the two-lamp
defect in the MF radical of the quotient, while the ambient normal form
keeps that defect nontrivial — the marked commutator of the ambient
group is exactly the killed sign, and the surviving two-lamp product is
detected by the signed finite-support model.

Consequently the sign-free quotient of EVERY marked compression datum
with Kazhdan source and proper witness element is non-MF: killing the
Clifford sign does not remove non-MF-ness, it reveals the finite-orbit
collapse underneath.  Instantiated at the literal affine datum this
resolves the commuting-lamp fork negatively: the witness quotient
`W/⟨ζ⟩` admits no injective corona representation.
-/

namespace GroupApproximation
namespace CommutingLampCollapse

open MarkedCompression CliffordLamp SemidirectProduct InvolutionCollapseEndpoint
open scoped commutatorElement

/-! ## Order-two powers -/

theorem zpow_mem_pair {H : Type*} [Group H] {s : H} (hs : s ^ 2 = 1)
    (n : ℤ) : s ^ n = 1 ∨ s ^ n = s := by
  have hss : s * s = 1 := by
    rw [← pow_two]
    exact hs
  have hinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have hnat : ∀ k : ℕ, s ^ k = 1 ∨ s ^ k = s := by
    intro k
    induction k with
    | zero =>
      left
      rw [pow_zero]
    | succ i ih =>
      rcases ih with h | h
      · right
        rw [pow_succ, h, one_mul]
      · left
        rw [pow_succ, h, hss]
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · rw [zpow_natCast]
    exact hnat k
  · rw [zpow_neg, zpow_natCast]
    rcases hnat k with h | h
    · left
      rw [h, inv_one]
    · right
      rw [h, hinv]

/-! ## The lamp-product discriminator -/

theorem lamp_mul_lamp_inv_ne {X : Type*} {x y : X} (h : x ≠ y) :
    lamp X x * (lamp X y)⁻¹ ≠ 1 ∧ lamp X x * (lamp X y)⁻¹ ≠ sign X := by
  classical
  letI : LinearOrder X := IsWellOrder.linearOrder WellOrderingRel
  have hval : (toModel X (lamp X x * (lamp X y)⁻¹)).config =
      Finsupp.single x 1 + Finsupp.single y 1 := by
    rw [map_mul, map_inv, toModel_lamp, toModel_lamp]
    simp [mul_def, inv_def, modelLamp]
  have hne0 : (Finsupp.single x (1 : ZMod 2) + Finsupp.single y 1) ≠ 0 := by
    intro hc
    have h1 := congrArg (fun f : X →₀ ZMod 2 ↦ f x) hc
    simp only [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.coe_zero,
      Pi.zero_apply] at h1
    rw [Finsupp.single_eq_of_ne h, add_zero] at h1
    exact one_ne_zero h1
  constructor
  · intro hc
    rw [hc, map_one] at hval
    exact hne0 (hval.symm.trans rfl)
  · intro hc
    rw [hc, toModel_sign] at hval
    exact hne0 (hval.symm.trans rfl)

/-! ## The sign subgroup is normal -/

instance signZpowers_normal {Γ : Type} [Group Γ] {α : Γ →* Γ}
    {hα : Function.Injective α} :
    (Subgroup.zpowers (signAmbient α hα)).Normal := by
  constructor
  intro x hx g
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hc : signAmbient α hα ^ n * g = g * signAmbient α hα ^ n :=
    ((signAmbient_central α hα g).zpow_left n).eq
  have h1 : g * signAmbient α hα ^ n * g⁻¹ = signAmbient α hα ^ n := by
    rw [← hc, mul_assoc, mul_inv_cancel, mul_one]
  rw [h1]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) n

/- Quotients of countable groups are countable.  Proved once as
`GroupApproximation.CountableInstances.quotientCountable` and taken here with
the same `local` scope the mirrored copy had. -/
attribute [local instance] GroupApproximation.CountableInstances.quotientCountable

variable {Γ : Type} [Group Γ] (α : Γ →* Γ) (hα : Function.Injective α)

/-! ## The ambient commutator in lamp coordinates -/

theorem commutator_iota_lampConj (a₀ : Γ) :
    ⁅iotaAmbient α hα a₀,
      tAmbient α hα * cAmbient α hα * (tAmbient α hα)⁻¹⁆ =
    inl (lamp (Cosets α hα)
        ((iotaVertical α hα a₀ * tVertical α hα) • rootCoset α hα) *
      (lamp (Cosets α hα) (tVertical α hα • rootCoset α hα))⁻¹) := by
  have hd : tAmbient α hα * cAmbient α hα * (tAmbient α hα)⁻¹ =
      inl (lamp (Cosets α hα) (tVertical α hα • rootCoset α hα)) :=
    conj_inl_lamp α hα _ _
  have hconj : iotaAmbient α hα a₀ *
      inl (lamp (Cosets α hα) (tVertical α hα • rootCoset α hα)) *
      (iotaAmbient α hα a₀)⁻¹ =
      inl (lamp (Cosets α hα)
        ((iotaVertical α hα a₀ * tVertical α hα) • rootCoset α hα)) := by
    have h1 := conj_inl_lamp α hα (iotaVertical α hα a₀)
      (tVertical α hα • rootCoset α hα)
    rw [smul_smul] at h1
    exact h1
  rw [hd, commutatorElement_def, hconj, ← map_inv, ← map_mul]

/-! ## The generic collapse of the sign-free quotient -/

/-- **The sign-free commuting-lamp quotient of a marked compression datum
is not MF.**  The two-lamp defect lies in the MF radical of the quotient
by the central sign, survives there, and obstructs every injective
corona representation. -/
theorem commutingLampQuotient_collapse :
    ∀ {Γ : Type} [Group Γ] (α : Γ →* Γ) (hα : Function.Injective α)
      (_hT : HasKazhdanPropertyT.{0, 0} Γ) [Countable (Ambient α hα)]
      {a₀ : Γ} (_ha₀ : a₀ ∉ Set.range α),
    (⁅(QuotientGroup.mk' (Subgroup.zpowers (signAmbient α hα)))
        (iotaAmbient α hα a₀),
      (QuotientGroup.mk' (Subgroup.zpowers (signAmbient α hα)))
        (tAmbient α hα * cAmbient α hα * (tAmbient α hα)⁻¹)⁆ ∈
      actualCoronaMFResidual
        (Ambient α hα ⧸ Subgroup.zpowers (signAmbient α hα))) ∧
    ⁅(QuotientGroup.mk' (Subgroup.zpowers (signAmbient α hα)))
        (iotaAmbient α hα a₀),
      (QuotientGroup.mk' (Subgroup.zpowers (signAmbient α hα)))
        (tAmbient α hα * cAmbient α hα * (tAmbient α hα)⁻¹)⁆ ≠ 1 ∧
    ¬ IsCDEOperatorMF
      (Ambient α hα ⧸ Subgroup.zpowers (signAmbient α hα)) := by
  intro Γ _ α hα hT _ a₀ ha₀
  classical
  haveI : Countable (Ambient α hα ⧸ Subgroup.zpowers (signAmbient α hα)) :=
    Function.Surjective.countable
      (QuotientGroup.mk'_surjective (Subgroup.zpowers (signAmbient α hα)))
  set q := QuotientGroup.mk' (Subgroup.zpowers (signAmbient α hα)) with hqdef
  set f : Γ →* Ambient α hα ⧸ Subgroup.zpowers (signAmbient α hα) :=
    q.comp (iotaAmbient α hα) with hfdef
  have hT' : HasKazhdanPropertyT.{0, 0} ↥f.range :=
    HasKazhdanPropertyT.of_surjective f.rangeRestrict
      (MonoidHom.rangeRestrict_surjective f) hT
  have hd : tAmbient α hα * cAmbient α hα * (tAmbient α hα)⁻¹ =
      inl (lamp (Cosets α hα) (tVertical α hα • rootCoset α hα)) :=
    conj_inl_lamp α hα _ _
  -- ambient compression identity
  have hambcomp : ∀ γ : Γ,
      tAmbient α hα * iotaAmbient α hα γ * (tAmbient α hα)⁻¹ =
        iotaAmbient α hα (α γ) := by
    intro γ
    show inr (tVertical α hα) * inr (iotaVertical α hα γ) *
        (inr (tVertical α hα))⁻¹ = inr (iotaVertical α hα (α γ))
    rw [← map_inv, ← map_mul, ← map_mul, vertical_compress]
  -- the compressed copy fixes the moved site
  have hsite : ∀ γ : Γ,
      iotaVertical α hα (α γ) • (tVertical α hα • rootCoset α hα) =
        tVertical α hα • rootCoset α hα := by
    intro γ
    have h1 := vertical_compress α hα γ
    have h2 : iotaVertical α hα (α γ) * tVertical α hα =
        tVertical α hα * iotaVertical α hα γ := by
      rw [← h1]
      group
    rw [smul_smul, h2, mul_smul, iotaVertical_smul_rootCoset]
  have hcommAmb : ∀ γ : Γ,
      Commute (iotaAmbient α hα (α γ))
        (inl (lamp (Cosets α hα) (tVertical α hα • rootCoset α hα)) :
          Ambient α hα) := by
    intro γ
    have h1 := conj_inl_lamp α hα (iotaVertical α hα (α γ))
      (tVertical α hα • rootCoset α hα)
    rw [hsite γ] at h1
    exact mul_inv_eq_iff_eq_mul.mp h1
  -- quotient-side compression
  have hconjq : ∀ γ : Γ,
      q (tAmbient α hα) * f γ * (q (tAmbient α hα))⁻¹ =
        f (α γ) := by
    intro γ
    show q (tAmbient α hα) * q (iotaAmbient α hα γ) *
        (q (tAmbient α hα))⁻¹ = q (iotaAmbient α hα (α γ))
    rw [← map_inv, ← map_mul, ← map_mul, hambcomp]
  have hcomp : ∀ γ' ∈ f.range,
      q (tAmbient α hα) * γ' * (q (tAmbient α hα))⁻¹ ∈ f.range := by
    intro γ' hγ'
    obtain ⟨γ, rfl⟩ := MonoidHom.mem_range.mp hγ'
    exact MonoidHom.mem_range.mpr ⟨α γ, (hconjq γ).symm⟩
  -- the witness
  have hk : IsInvolutiveCompressionWitness f.range (q (tAmbient α hα))
      (q (tAmbient α hα * cAmbient α hα * (tAmbient α hα)⁻¹)) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [← map_mul]
      have hk₀ : (tAmbient α hα * cAmbient α hα * (tAmbient α hα)⁻¹) *
          (tAmbient α hα * cAmbient α hα * (tAmbient α hα)⁻¹) = 1 := by
        rw [hd, ← map_mul, ← pow_two, lamp_sq, map_one]
      rw [hk₀, map_one]
    · intro γ' hγ'
      obtain ⟨γ, rfl⟩ := MonoidHom.mem_range.mp hγ'
      rw [hconjq γ, hd]
      exact ((hcommAmb γ).map q)
    · intro γ₁' hγ₁' γ₂' hγ₂'
      obtain ⟨γ₁, rfl⟩ := MonoidHom.mem_range.mp hγ₁'
      obtain ⟨γ₂, rfl⟩ := MonoidHom.mem_range.mp hγ₂'
      have hlampconj : ∀ γ : Γ,
          f γ * q (tAmbient α hα * cAmbient α hα * (tAmbient α hα)⁻¹) *
            (f γ)⁻¹ =
          q (inl (lamp (Cosets α hα)
            ((iotaVertical α hα γ * tVertical α hα) • rootCoset α hα))) := by
        intro γ
        rw [hd]
        show q (iotaAmbient α hα γ) *
            q (inl (lamp (Cosets α hα)
              (tVertical α hα • rootCoset α hα))) *
            (q (iotaAmbient α hα γ))⁻¹ = _
        rw [← map_inv, ← map_mul, ← map_mul]
        congr 1
        have h1 := conj_inl_lamp α hα (iotaVertical α hα γ)
          (tVertical α hα • rootCoset α hα)
        rw [smul_smul] at h1
        exact h1
      rw [hlampconj γ₁, hlampconj γ₂]
      rcases eq_or_ne
        ((iotaVertical α hα γ₁ * tVertical α hα) • rootCoset α hα)
        ((iotaVertical α hα γ₂ * tVertical α hα) • rootCoset α hα) with
        heq | hne
      · rw [heq]
      · refine commutatorElement_eq_one_iff_commute.mp ?_
        rw [← map_commutatorElement, ← map_commutatorElement,
          commutator_lamp_lamp (Cosets α hα) hne]
        exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_zpowers _)
  -- nontriviality
  have hx12 : (iotaVertical α hα a₀ * tVertical α hα) • rootCoset α hα ≠
      tVertical α hα • rootCoset α hα :=
    (moved_cosets_ne α hα ha₀).symm
  have hlampne := lamp_mul_lamp_inv_ne (X := Cosets α hα) hx12
  have hne1 : ⁅q (iotaAmbient α hα a₀),
      q (tAmbient α hα * cAmbient α hα * (tAmbient α hα)⁻¹)⁆ ≠ 1 := by
    rw [← map_commutatorElement, commutator_iota_lampConj]
    intro hc
    have hmem := (QuotientGroup.eq_one_iff _).mp hc
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
    rcases zpow_mem_pair (signAmbient_sq α hα) n with h0 | h0 <;>
      rw [h0] at hn
    · have h2 : (inl (lamp (Cosets α hα)
          ((iotaVertical α hα a₀ * tVertical α hα) • rootCoset α hα) *
          (lamp (Cosets α hα)
            (tVertical α hα • rootCoset α hα))⁻¹) : Ambient α hα) =
          inl 1 := by
        rw [map_one]
        exact hn.symm
      exact hlampne.1 (inl_injective h2)
    · have h2 : (inl (lamp (Cosets α hα)
          ((iotaVertical α hα a₀ * tVertical α hα) • rootCoset α hα) *
          (lamp (Cosets α hα)
            (tVertical α hα • rootCoset α hα))⁻¹) : Ambient α hα) =
          inl (sign (Cosets α hα)) := hn.symm
      exact hlampne.2 (inl_injective h2)
  -- endpoint
  have hγL : q (iotaAmbient α hα a₀) ∈ f.range :=
    MonoidHom.mem_range.mpr ⟨a₀, rfl⟩
  refine ⟨?_, hne1, ?_⟩
  · exact InvolutionCollapseEndpoint.actualCoronaMFInvisible_of_involutiveWitness
      hT' hcomp hk hγL
  · exact ProjectionCompressionCollapse.not_isCDEOperatorMF_of_involutiveWitness
      hT' hcomp hk hγL hne1

/-! ## The literal instance: the witness quotient is not MF -/

section Literal

open LiteralNonMFLinearWitness LiteralBaseAffineQuotient
  LiteralBaseP13PropertyTBridge ExplicitLinearModel LiteralNonMFPresentation

/-- Property (T) for the concrete affine matrix base, by pushing the
presented base's certificate through the affine quotient. -/
theorem gammaBar_hasKazhdanPropertyT : HasKazhdanPropertyT.{0, 0} gammaBar :=
  HasKazhdanPropertyT.of_surjective affineQuotient affineQuotient_surjective
    (manuscriptBaseHasKazhdanPropertyT.{0}).1

instance witnessGroup_countable :
    Countable (Ambient alpha conjD_injective) :=
  Function.Surjective.countable witnessHom_surjective

/-- **The literal commuting-lamp quotient is not MF**: the sign-free
quotient of the concrete affine--Clifford witness carries its two-lamp
defect inside the MF radical, and the defect survives. -/
theorem literalCommutingLampQuotient_collapse :
    (⁅(QuotientGroup.mk'
        (Subgroup.zpowers (signAmbient alpha conjD_injective)))
        (iotaAmbient alpha conjD_injective v1G),
      (QuotientGroup.mk'
        (Subgroup.zpowers (signAmbient alpha conjD_injective)))
        (tAmbient alpha conjD_injective * cAmbient alpha conjD_injective *
          (tAmbient alpha conjD_injective)⁻¹)⁆ ∈
      actualCoronaMFResidual
        (Ambient alpha conjD_injective ⧸
          Subgroup.zpowers (signAmbient alpha conjD_injective))) ∧
    ⁅(QuotientGroup.mk'
        (Subgroup.zpowers (signAmbient alpha conjD_injective)))
        (iotaAmbient alpha conjD_injective v1G),
      (QuotientGroup.mk'
        (Subgroup.zpowers (signAmbient alpha conjD_injective)))
        (tAmbient alpha conjD_injective * cAmbient alpha conjD_injective *
          (tAmbient alpha conjD_injective)⁻¹)⁆ ≠ 1 ∧
    ¬ IsCDEOperatorMF
      (Ambient alpha conjD_injective ⧸
        Subgroup.zpowers (signAmbient alpha conjD_injective)) :=
  commutingLampQuotient_collapse alpha conjD_injective
    gammaBar_hasKazhdanPropertyT v1G_not_mem_range

/-- The literal commuting-lamp quotient admits no injective corona
representation. -/
theorem literalCommutingLampQuotient_not_isCDEOperatorMF :
    ¬ IsCDEOperatorMF
      (Ambient alpha conjD_injective ⧸
        Subgroup.zpowers (signAmbient alpha conjD_injective)) :=
  literalCommutingLampQuotient_collapse.2.2

end Literal

end CommutingLampCollapse
end GroupApproximation
