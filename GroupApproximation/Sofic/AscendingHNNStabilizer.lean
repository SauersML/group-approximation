import GroupApproximation.Sofic.MarkedCompressionGroup

/-!
# The witness site of the ascending HNN construction

**Section 34.1** of the dossier.  The correct site for the compression witness is
`t Γ`, not the base coset, and its stabiliser inside `Γ` is exactly the image of
the compressing endomorphism.

Consequently properness of the self-embedding is precisely what supplies a mover:
every `γ ∉ α(Γ)` moves the site, so the corresponding lamp defect is nontrivial,
while every `γ ∈ α(Γ)` fixes it, which is the centrality hypothesis of the
collapse theorem.

Specializing the collapse criterion to the ascending HNN extension of a
property-`(T)` group along a proper injective self-embedding — so that a
non-co-Hopfian Kazhdan group is the only structural input needed — was
suggested by Francesco Fournier-Facio, as was the observation that the ambient
group then need not have `(T)` at all, in contrast with the Kun--Thom
examples.
-/

namespace GroupApproximation
namespace MarkedCompression

open MappingTelescope

universe u

variable {Γ : Type u} [Group Γ] (α : Γ →* Γ) (hα : Function.Injective α)

/-- The witness site: the image of the base coset under the stable letter. -/
def tSite : Cosets α hα := tVertical α hα • rootCoset α hα

/-- **The compressed copy fixes the witness site.**  This is the centrality
half of Section 34.1. -/
theorem iotaVertical_range_smul_tSite (δ : Γ) :
    iotaVertical α hα (α δ) • tSite α hα = tSite α hα := by
  have hcomp : iotaVertical α hα (α δ)
      = tVertical α hα * iotaVertical α hα δ * (tVertical α hα)⁻¹ :=
    (vertical_compress α hα δ).symm
  rw [tSite, hcomp, mul_smul, mul_smul, inv_smul_smul,
    iotaVertical_smul_rootCoset]

include hα in
/-- **Everything outside the image moves the witness site.**  This is the mover
half of Section 34.1, and it is exactly where properness of the self-embedding
enters. -/
theorem not_smul_tSite_of_not_mem_range {a₀ : Γ} (ha₀ : a₀ ∉ Set.range α) :
    iotaVertical α hα a₀ • tSite α hα ≠ tSite α hα := by
  intro hcon
  refine moved_cosets_ne α hα ha₀ ?_
  rw [mul_smul]
  exact (hcon.symm : _)

include hα in
/-- **Section 34.1.**  The stabiliser of the witness site inside the base copy is
exactly the image of the compressing endomorphism. -/
theorem smul_tSite_eq_iff (γ : Γ) :
    iotaVertical α hα γ • tSite α hα = tSite α hα ↔ γ ∈ Set.range α := by
  constructor
  · intro h
    by_contra hcon
    exact not_smul_tSite_of_not_mem_range α hα hcon h
  · rintro ⟨δ, rfl⟩
    exact iotaVertical_range_smul_tSite α hα δ

end MarkedCompression
end GroupApproximation
