import GroupApproximation.Sofic.AscendingHNNFullTelescopeRadical
import GroupApproximation.Sofic.TorsionSpectralCollapse
import GroupApproximation.Algebra.CountableInstances
import GroupApproximation.Meta.AxiomGuard

/-!
# Spectral motion at every finite lamp order, over the whole telescope

**thm:notes-visible-quotient**, first step of the proof: in every corona
representation the lamp values at two sites of the same height are identified.

`Sofic/AscendingHNNFullTelescopeRadical` proves this for an *involutive* lamp
value.  Here we prove it for every lamp value of finite order, using the
unconditional torsion collapse
`TorsionSpectralCollapse.actualCoronaMFInvisible_of_torsionWitness`.  The
argument is the same.  The level-`n` copy `Γₙ` of the base is Kazhdan, `tⁿ`
compresses it onto the base, and the base fixes the root coset.  So the
one-site lamp at the root is a torsion compression witness for `(Γₙ, tⁿ)`.
Since every telescope element comes from some level, every equal-height lamp
difference is invisible.

* `isTorsionCompressionWitness_rootLamp` -- the witness, at every level.
* `lampDiff_level_mem_actualCoronaMFResidual_of_pow` -- one level.
* `lampDiff_mem_actualCoronaMFResidual_of_rightHom_eq_of_pow` -- any two sites
  of equal height, for any lamp value of finite order.
-/

namespace GroupApproximation.Full.NN04

open SemidirectProduct MappingTelescope MarkedCompression TorsionCompressionCollapse
open scoped commutatorElement

variable {Γ₀ : Type} [Group Γ₀] (β : Γ₀ →* Γ₀) (hβ : Function.Injective β)
variable {K₀ : Type} [Group K₀] [DecidableEq (Cosets β hβ)]

/-- A finite-order lamp value at the root has a finite-order root lamp. -/
theorem rootLamp_pow_eq_one {k₀ : K₀} {m : ℕ} (hk : k₀ ^ m = 1) :
    rootLamp β hβ k₀ ^ m = 1 := by
  have hsingle : Lamp.single (rootCoset β hβ) k₀ ^ m = 1 := by
    have h1 := map_pow (Lamp.singleHom (K := K₀) (rootCoset β hβ)) k₀ m
    rw [hk, map_one, Lamp.singleHom_apply] at h1
    exact h1.symm
  rw [rootLamp, ← map_pow, hsingle, map_one]

/-- **The root lamp is a torsion compression witness at every level.**  The
compressed copy of the level-`n` group is the base, which fixes the root coset.
Its conjugates are one-site lamps, and these commute pairwise. -/
theorem isTorsionCompressionWitness_rootLamp {k₀ : K₀} {m : ℕ} (hm : 0 < m)
    (hk : k₀ ^ m = 1) (n : ℕ) :
    IsTorsionCompressionWitness (levelSub (K₀ := K₀) β hβ n)
      (wreathT β hβ ^ n) (rootLamp β hβ k₀) := by
  refine ⟨⟨m, hm, rootLamp_pow_eq_one β hβ hk⟩, ?_, ?_⟩
  · intro w hw
    obtain ⟨γ, rfl⟩ := (mem_levelSub_iff β hβ).mp hw
    have hconj : wreathT β hβ ^ n *
        (inr (levelHom β hβ n γ) : WreathV (K := K₀) β hβ) *
        (wreathT β hβ ^ n)⁻¹ = inr (iotaVertical β hβ γ) := by
      rw [wreathT, ← map_pow, ← map_inv, ← map_mul, ← map_mul,
        tpow_conj_levelHom]
    rw [hconj]
    have hfix : (inr (iotaVertical β hβ γ) : WreathV (K := K₀) β hβ) *
        rootLamp β hβ k₀ * (inr (iotaVertical β hβ γ))⁻¹
        = rootLamp β hβ k₀ := by
      rw [conj_rootLamp, iotaVertical_smul_rootCoset]
      rfl
    exact mul_inv_eq_iff_eq_mul.mp hfix
  · intro w₁ h₁ w₂ h₂
    obtain ⟨γ₁, rfl⟩ := (mem_levelSub_iff β hβ).mp h₁
    obtain ⟨γ₂, rfl⟩ := (mem_levelSub_iff β hβ).mp h₂
    rw [conj_rootLamp, conj_rootLamp]
    have hbase := conj_single_commute (K := K₀) (levelHom β hβ n γ₁)
      (levelHom β hβ n γ₂) (rootCoset β hβ) k₀
    rw [lampAut_single, lampAut_single] at hbase
    exact (show Commute _ _ from hbase).map
      (inl : Lamp K₀ (Cosets β hβ) →* WreathV (K := K₀) β hβ)

include hβ in
/-- **One level, finite order.**  The lamp difference between the root coset
and any of its level-`n` translates lies in the MF radical. -/
theorem lampDiff_level_mem_actualCoronaMFResidual_of_pow
    [Countable (WreathV (K := K₀) β hβ)]
    (hΓ : HasKazhdanPropertyT.{0, 0} Γ₀) {k₀ : K₀} {m : ℕ} (hm : 0 < m)
    (hk : k₀ ^ m = 1) (n : ℕ) (γ : Γ₀) :
    lampDiff β hβ (levelHom β hβ n γ • rootCoset β hβ) (rootCoset β hβ) k₀
      ∈ actualCoronaMFResidual (WreathV (K := K₀) β hβ) := by
  have hinv := TorsionSpectralCollapse.actualCoronaMFInvisible_of_torsionWitness
    (levelSub_hasKazhdanPropertyT β hβ hΓ n)
    (fun _ hw => wreathT_pow_compress β hβ hw)
    (isTorsionCompressionWitness_rootLamp β hβ hm hk n)
    ((mem_levelSub_iff β hβ).mpr ⟨γ, rfl⟩)
  rw [commutator_rootLamp_eq_lampDiff] at hinv
  exact mem_actualCoronaMFResidual_iff.mpr hinv

include hβ in
/-- **The whole telescope, at the root, finite order.** -/
theorem lampDiff_telescope_mem_actualCoronaMFResidual_of_pow
    [Countable (WreathV (K := K₀) β hβ)]
    (hΓ : HasKazhdanPropertyT.{0, 0} Γ₀) {k₀ : K₀} {m : ℕ} (hm : 0 < m)
    (hk : k₀ ^ m = 1) (a : Telescope β hβ) :
    lampDiff β hβ ((inl a : Vertical β hβ) • rootCoset β hβ)
        (rootCoset β hβ) k₀
      ∈ actualCoronaMFResidual (WreathV (K := K₀) β hβ) := by
  induction a using Quotient.inductionOn with | h p =>
  obtain ⟨n, γ⟩ := p
  exact lampDiff_level_mem_actualCoronaMFResidual_of_pow β hβ hΓ hm hk n γ

include hβ in
/-- **Translated, finite order.** -/
theorem lampDiff_translate_mem_actualCoronaMFResidual_of_pow
    [Countable (WreathV (K := K₀) β hβ)]
    (hΓ : HasKazhdanPropertyT.{0, 0} Γ₀) {k₀ : K₀} {m : ℕ} (hm : 0 < m)
    (hk : k₀ ^ m = 1) (g : Vertical β hβ) (a : Telescope β hβ) :
    lampDiff β hβ ((g * inl a) • rootCoset β hβ) (g • rootCoset β hβ) k₀
      ∈ actualCoronaMFResidual (WreathV (K := K₀) β hβ) := by
  have hconj := (inferInstance :
      (actualCoronaMFResidual (WreathV (K := K₀) β hβ)).Normal).conj_mem _
    (lampDiff_telescope_mem_actualCoronaMFResidual_of_pow β hβ hΓ hm hk a)
    (inr g)
  rwa [conj_lampDiff, ← mul_smul] at hconj

include hβ in
/-- **thm:notes-visible-quotient, spectral-motion step.**  For a lamp value of
finite order, the lamp difference between two sites of equal height is
invisible to every corona representation. -/
theorem lampDiff_mem_actualCoronaMFResidual_of_rightHom_eq_of_pow
    [Countable (WreathV (K := K₀) β hβ)]
    (hΓ : HasKazhdanPropertyT.{0, 0} Γ₀) {k₀ : K₀} {m : ℕ} (hm : 0 < m)
    (hk : k₀ ^ m = 1) {v w : Vertical β hβ} (h : rightHom v = rightHom w) :
    lampDiff β hβ (v • rootCoset β hβ) (w • rootCoset β hβ) k₀
      ∈ actualCoronaMFResidual (WreathV (K := K₀) β hβ) := by
  have hker : v⁻¹ * w ∈ (rightHom : Vertical β hβ →* Multiplicative ℤ).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  rw [← SemidirectProduct.range_inl_eq_ker_rightHom] at hker
  obtain ⟨a, ha⟩ := hker
  have hw : w = v * inl a := by rw [ha]; group
  have hmem := lampDiff_translate_mem_actualCoronaMFResidual_of_pow β hβ hΓ hm hk
    v a
  rw [← hw] at hmem
  have hinv := (actualCoronaMFResidual (WreathV (K := K₀) β hβ)).inv_mem hmem
  rwa [lampDiff_inv] at hinv

#audit_axioms rootLamp_pow_eq_one
#audit_axioms isTorsionCompressionWitness_rootLamp
#audit_axioms lampDiff_level_mem_actualCoronaMFResidual_of_pow
#audit_axioms lampDiff_mem_actualCoronaMFResidual_of_rightHom_eq_of_pow

end GroupApproximation.Full.NN04
