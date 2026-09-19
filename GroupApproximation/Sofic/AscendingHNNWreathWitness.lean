import GroupApproximation.Algebra.PermutationalWreathSimple
import GroupApproximation.Sofic.AscendingHNNStabilizer
import GroupApproximation.Sofic.TorsionCompressionCollapse
import GroupApproximation.Sofic.ProjectionCompressionCollapse
import GroupApproximation.Sofic.WreathWitnessGeneric

/-!
# The ascending-HNN lamp is a torsion compression witness

**Sections 34.2--34.4** of the dossier, in their algebraic form: the structural
input that a proper injective self-embedding of a group supplies to the
compression-collapse theorem.

Take any group `Γ`, an injective `α : Γ → Γ`, the ascending HNN model
`V = Vertical α hα`, its coset space `X = Cosets α hα`, and any lamp group `K`.
Inside the permutational wreath product `Wreath K V X`, put

* `L` = the base copy of `Γ`,
* `s` = the stable letter,
* `k` = the one-site lamp carrying a value `k₀` at the witness site `t Γ`.

Then `k` is a torsion compression witness for `(L, s)` as soon as `k₀` has
finite order, and every `γ ∉ α(Γ)` gives a *nontrivial* collapse commutator.

The three witness conditions are **not** proved here.  They are the general
permutational-wreath sentence of the manuscript --- any lamp group, any site
set, any acting group, any compressed subgroup --- and they live in
`Sofic.WreathWitnessGeneric`.  This file supplies only the ascending-HNN input
those conditions consume: that the compressed copy fixes the witness site
(`iotaVertical_range_smul_tSite`).  What remains specific to the construction
is nontriviality, which uses properness through `smul_tSite_eq_iff`.

Specializing the collapse criterion this way — so that a non-co-Hopfian
Kazhdan group is the only structural input — was suggested by Francesco
Fournier-Facio.

What is *not* here is the analytic gate: `torsionCollapseDefect_le_actualCoronaMFResidual`
still takes the collapse hypothesis `hkill`, discharged unconditionally only for
the involutive subclass in `Sofic/InvolutionCollapseEndpoint`.  This file
supplies the group theory that feeds it.
-/

namespace GroupApproximation
namespace MarkedCompression

open SemidirectProduct MappingTelescope TorsionCompressionCollapse
open scoped commutatorElement

universe u v

variable {Γ : Type u} [Group Γ] (α : Γ →* Γ) (hα : Function.Injective α)
variable {K : Type v} [Group K] [DecidableEq (Cosets α hα)]

/-- The ambient wreath product of the ascending-HNN construction. -/
abbrev WreathV : Type (max u v) := Wreath K (Vertical α hα) (Cosets α hα)

/-- The base copy of `Γ` inside the wreath product. -/
def baseSub : Subgroup (WreathV (K := K) α hα) :=
  ((inr : Vertical α hα →* WreathV (K := K) α hα).comp
    (iotaVertical α hα)).range

/-- The stable letter inside the wreath product. -/
def wreathT : WreathV (K := K) α hα := inr (tVertical α hα)

/-- The witness lamp: the value `k₀` placed at the witness site `t Γ`. -/
def witnessLamp (k₀ : K) : WreathV (K := K) α hα :=
  inl (Lamp.single (tSite α hα) k₀)

omit [DecidableEq (Cosets α hα)] in
theorem mem_baseSub_iff {w : WreathV (K := K) α hα} :
    w ∈ baseSub α hα ↔ ∃ γ : Γ, inr (iotaVertical α hα γ) = w := by
  simp [baseSub, MonoidHom.mem_range]

/-- Conjugating the witness lamp by a base element moves it to the translated
site. -/
theorem conj_witnessLamp (γ : Γ) (k₀ : K) :
    (inr (iotaVertical α hα γ) : WreathV (K := K) α hα) * witnessLamp α hα k₀ *
        (inr (iotaVertical α hα γ))⁻¹
      = inl (Lamp.single (iotaVertical α hα γ • tSite α hα) k₀) :=
  conj_inl_single K (Vertical α hα) (Cosets α hα) _ _ _

/-- **The witness is torsion** as soon as its value is.  The witness lamp *is*
the generic one-site lamp `WreathWitness.siteLamp` at the witness site, so this
is that module's general statement read here. -/
theorem witnessLamp_pow (k₀ : K) (m : ℕ) (hk : k₀ ^ m = 1) :
    witnessLamp α hα k₀ ^ m = 1 :=
  WreathWitness.siteLamp_pow (G := Vertical α hα) (tSite α hα) k₀ m hk

omit [DecidableEq (Cosets α hα)] in
/-- **The ascending-HNN input to the wreath sentence.**  Every element of the
base copy is an `inr` of the acting group, and its `t`-conjugate fixes the
witness site: that is exactly the manuscript's "`x₀ ∈ X` a point fixed by
`s L s⁻¹`" for this `L` and this `s`. -/
theorem baseSub_compressed_fixes_tSite :
    ∀ w ∈ baseSub (K := K) α hα, ∃ g : Vertical α hα,
      (inr g : WreathV (K := K) α hα) = w ∧
        (tVertical α hα * g * (tVertical α hα)⁻¹) • tSite α hα = tSite α hα := by
  intro w hw
  obtain ⟨γ, rfl⟩ := (mem_baseSub_iff α hα).mp hw
  refine ⟨iotaVertical α hα γ, rfl, ?_⟩
  rw [vertical_compress]
  exact iotaVertical_range_smul_tSite α hα γ

/-- **The compressed copy centralises the witness.**  The centrality condition
`(W2)`, read off the general wreath sentence: the compressed copy fixes the
witness site. -/
theorem commute_compressed_witnessLamp (k₀ : K) {w : WreathV (K := K) α hα}
    (hw : w ∈ baseSub α hα) :
    Commute (wreathT α hα * w * (wreathT α hα)⁻¹) (witnessLamp α hα k₀) := by
  obtain ⟨γ, rfl⟩ := (mem_baseSub_iff α hα).mp hw
  have hconj : wreathT α hα *
      (inr (iotaVertical α hα γ) : WreathV (K := K) α hα) * (wreathT α hα)⁻¹
      = inr (iotaVertical α hα (α γ)) := by
    rw [wreathT, ← map_inv, ← map_mul, ← map_mul, vertical_compress]
  rw [hconj]
  exact WreathWitness.commute_inr_siteLamp (iotaVertical α hα (α γ))
    (tSite α hα) k₀ (iotaVertical_range_smul_tSite α hα γ)

/-- **The conjugation orbit of the witness commutes.**  The commuting-orbit
condition `(W3)`, read off the general wreath sentence: one-site lamps at
distinct sites commute, and conjugation only moves the site. -/
theorem commute_orbit_witnessLamp (k₀ : K) {w₁ w₂ : WreathV (K := K) α hα}
    (hw₁ : w₁ ∈ baseSub α hα) (hw₂ : w₂ ∈ baseSub α hα) :
    Commute (w₁ * witnessLamp α hα k₀ * w₁⁻¹)
      (w₂ * witnessLamp α hα k₀ * w₂⁻¹) := by
  obtain ⟨γ₁, rfl⟩ := (mem_baseSub_iff α hα).mp hw₁
  obtain ⟨γ₂, rfl⟩ := (mem_baseSub_iff α hα).mp hw₂
  exact WreathWitness.commute_conj_siteLamp (iotaVertical α hα γ₁)
    (iotaVertical α hα γ₂) (tSite α hα) k₀

/-- **Sections 34.2--34.3.**  The one-site lamp at the witness site is a
torsion compression witness for the base copy and the stable letter. -/
theorem isTorsionCompressionWitness_witnessLamp (k₀ : K) (m : ℕ) (hm : 0 < m)
    (hk : k₀ ^ m = 1) :
    IsTorsionCompressionWitness (baseSub α hα) (wreathT α hα)
      (witnessLamp α hα k₀) :=
  ⟨⟨m, hm, witnessLamp_pow α hα k₀ m hk⟩,
    fun _ hw => commute_compressed_witnessLamp α hα k₀ hw,
    fun _ h₁ _ h₂ => commute_orbit_witnessLamp α hα k₀ h₁ h₂⟩

/-- **Section 34.4, properness supplies a nontrivial defect.**  Every element
outside the image of the self-embedding gives a collapse commutator that is not
the identity. -/
theorem commutator_witnessLamp_ne_one {k₀ : K} (hk₀ : k₀ ≠ 1) {a₀ : Γ}
    (ha₀ : a₀ ∉ Set.range α) :
    ⁅(inr (iotaVertical α hα a₀) : WreathV (K := K) α hα),
      witnessLamp α hα k₀⁆ ≠ 1 := by
  have hsite : iotaVertical α hα a₀ • tSite α hα ≠ tSite α hα :=
    not_smul_tSite_of_not_mem_range α hα ha₀
  intro hcon
  rw [commutatorElement_def, conj_witnessLamp] at hcon
  rw [witnessLamp, ← map_inv, ← map_mul] at hcon
  have hlamp : Lamp.single (iotaVertical α hα a₀ • tSite α hα) k₀ *
      (Lamp.single (tSite α hα) k₀)⁻¹ = 1 := by
    have := congrArg (SemidirectProduct.left) hcon
    simpa using this
  refine single_mul_single_inv_ne_one (K := K) hsite hk₀ ?_
  rw [← hlamp]
  congr 1
  exact map_inv (Lamp.singleHom (K := K) (tSite α hα)) k₀

/-! ## The unconditional involutive endpoint -/

section Unconditional

variable {Γ₀ : Type} [Group Γ₀] (β : Γ₀ →* Γ₀) (hβ : Function.Injective β)
variable {K₀ : Type} [Group K₀] [DecidableEq (Cosets β hβ)]

omit [DecidableEq (Cosets β hβ)] in
include hβ in
/-- The base copy inside the wreath product is isomorphic to `Γ`, so it
inherits property `(T)`. -/
theorem baseSub_hasKazhdanPropertyT (hΓ : HasKazhdanPropertyT.{0, 0} Γ₀) :
    HasKazhdanPropertyT.{0, 0} ↥(baseSub (K := K₀) β hβ) := by
  have hf : Function.Injective
      ((inr : Vertical β hβ →* WreathV (K := K₀) β hβ).comp
        (iotaVertical β hβ)) :=
    inr_injective.comp (iotaVertical_injective β hβ)
  exact HasKazhdanPropertyT.of_mulEquiv (MonoidHom.ofInjective hf).symm hΓ

omit [DecidableEq (Cosets β hβ)] in
include hβ in
/-- The stable letter compresses the base copy: this is the HNN relation. -/
theorem wreathT_compress {w : WreathV (K := K₀) β hβ}
    (hw : w ∈ baseSub β hβ) :
    wreathT β hβ * w * (wreathT β hβ)⁻¹ ∈ baseSub (K := K₀) β hβ := by
  obtain ⟨γ, rfl⟩ := (mem_baseSub_iff β hβ).mp hw
  have hconj : wreathT β hβ *
      (inr (iotaVertical β hβ γ) : WreathV (K := K₀) β hβ) * (wreathT β hβ)⁻¹
      = inr (iotaVertical β hβ (β γ)) := by
    rw [wreathT, ← map_inv, ← map_mul, ← map_mul, vertical_compress]
  rw [hconj]
  exact (mem_baseSub_iff β hβ).mpr ⟨β γ, rfl⟩

include hβ in
/-- An involutive lamp value gives an involutive compression witness.  This is
the general permutational-wreath sentence of `Sofic.WreathWitnessGeneric`,
instantiated at the ascending-HNN site data; nothing is reproved here. -/
theorem isInvolutiveCompressionWitness_witnessLamp {k₀ : K₀}
    (hk2 : k₀ * k₀ = 1) :
    InvolutionCollapseEndpoint.IsInvolutiveCompressionWitness
      (baseSub β hβ) (wreathT β hβ) (witnessLamp β hβ k₀) :=
  WreathWitness.isInvolutiveCompressionWitness_siteLamp_zero
    (tVertical β hβ) (tSite β hβ) hk2
    (baseSub_compressed_fixes_tSite (K := K₀) β hβ)

include hβ in
/-- **The ascending-HNN endpoint, unconditional for involutive lamps.**  A
property-`(T)` group with a *proper* injective self-embedding gives a
permutational wreath product that is not MF: the one-site lamp at the witness
site is an involutive compression witness, and properness makes its commutator
with a mover nontrivial.

No soficity, residual finiteness or finite-index hypothesis is used. -/
theorem not_isCDEOperatorMF_wreath
    [Countable (WreathV (K := K₀) β hβ)]
    (hΓ : HasKazhdanPropertyT.{0, 0} Γ₀)
    {k₀ : K₀} (hk₀ : k₀ ≠ 1) (hk2 : k₀ * k₀ = 1)
    {a₀ : Γ₀} (ha₀ : a₀ ∉ Set.range β) :
    ¬ IsCDEOperatorMF (WreathV (K := K₀) β hβ) :=
  ProjectionCompressionCollapse.not_isCDEOperatorMF_of_involutiveWitness
    (baseSub_hasKazhdanPropertyT β hβ hΓ)
    (fun _ hw => wreathT_compress β hβ hw)
    (isInvolutiveCompressionWitness_witnessLamp β hβ hk2)
    ((mem_baseSub_iff β hβ).mpr ⟨a₀, rfl⟩)
    (commutator_witnessLamp_ne_one β hβ hk₀ ha₀)

end Unconditional

end MarkedCompression
end GroupApproximation
