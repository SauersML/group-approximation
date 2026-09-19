import GroupApproximation.Sofic.FreeLampReduction
import GroupApproximation.Sofic.SoficTransfer
import GroupApproximation.Sofic.Hyperlinear

/-!
# The central free-lamp cover

For a group `G` with a subgroup `Z`, the free-lamp amalgam
`FreeLamp G Z K = G *_Z (Z × K)` from `FreeLampReduction` specializes, when
`Z` is central, to a split cover of `G`.

This file proves exactly the local algebraic statements it exports: the
retraction onto the ambient group, subgroup monotonicity for soficity and
hyperlinearity, and the fact that the free-lamp escape condition is impossible
over a central base.  It contains no closure claim for amalgamated products
and accepts no such claim as a premise.
-/

namespace GroupApproximation

open Monoid

variable (G : Type) [Group G] (Z : Subgroup G) (K : Type) [Group K]

/-- The factorwise maps of the retraction: the identity on the ambient
group, the first coordinate on the lamp-augmented base. -/
def lampRetractMaps : ∀ b, LampFactor G Z K b →* G
  | true => MonoidHom.id G
  | false => Z.subtype.comp (MonoidHom.fst ↥Z K)

theorem lampRetractMaps_comp :
    ∀ b, (lampRetractMaps G Z K b).comp (lampMap G Z K b) = Z.subtype
  | true => by ext γ; rfl
  | false => by ext γ; rfl

/-- The retraction of the free-lamp amalgam onto its ambient group:
kill the lamps, keep the group. -/
def lampRetract : FreeLamp G Z K →* G :=
  PushoutI.lift (lampRetractMaps G Z K) Z.subtype (lampRetractMaps_comp G Z K)

@[simp] theorem lampRetract_inAmbient (g : G) :
    lampRetract G Z K (inAmbient G Z K g) = g := by
  rw [inAmbient_apply]
  exact PushoutI.lift_of _ _ _ _

/-- The cover splits over its base: the retraction is surjective. -/
theorem lampRetract_surjective : Function.Surjective (lampRetract G Z K) :=
  fun g => ⟨inAmbient G Z K g, lampRetract_inAmbient G Z K g⟩

/-- **Soficity of the cover forces soficity of the base** because the base
embeds. -/
theorem isSofic_base_of_cover (h : IsSofic (FreeLamp G Z K)) : IsSofic G :=
  isSofic_of_injective (inAmbient G Z K) (inAmbient_injective G Z K) h

/-- Hyperlinearity of the cover forces hyperlinearity of the base because the
base embeds. -/
theorem isHyperlinear_base_of_cover (h : IsHyperlinear (FreeLamp G Z K)) :
    IsHyperlinear G :=
  isHyperlinear_of_injective (inAmbient G Z K) (inAmbient_injective G Z K) h

/-- **No escape from a central base.**  The witness hypothesis of the
free-lamp reduction — some `γ ∈ Z` with `t⁻¹γt ∉ Z` — is unsatisfiable
when `Z` is central: conjugation fixes central elements.  So centralizer
normalization cannot decide the cover's soficity, and a nonsoficity proof
for a central cover requires a genuinely new mechanism. -/
theorem no_escape_of_central (hZ : Z ≤ Subgroup.center G) (t : G) {γ : G}
    (hγ : γ ∈ Z) : t⁻¹ * γ * t ∈ Z := by
  have hc : t⁻¹ * γ * t = γ := by
    have h := Subgroup.mem_center_iff.mp (hZ hγ)
    calc t⁻¹ * γ * t = t⁻¹ * (γ * t) := by group
      _ = t⁻¹ * (t * γ) := by rw [← h t]
      _ = γ := by group
  rw [hc]
  exact hγ

end GroupApproximation
