import GroupApproximation.Sofic.DoubleSoficTransfer
import GroupApproximation.Sofic.MFDefinitions
import GroupApproximation.Sofic.SoficSequential
import GroupApproximation.Sofic.SoficUltraproduct

/-!
# The operator-MF nonsofic symmetric-double endpoint

This file closes the formal group-theoretic part of the Kun--Thom--Shulman
argument.  It isolates the one recent Kun--Thom input as a mathematical
property of an inclusion `Γ ≤ G`: in every faithful permutation-ultraproduct
representation of `G`, the centralizer of `Γ` is normalized by `G`.

From that property and one strict compressor witness, Lean proves that

* every nontrivial free-lamp amalgam `G *_Γ (Γ × K)` is nonsofic; and
* the symmetric double `G *_Γ G` is nonsofic, using the proved flip
  identification and finite-extension permanence.

The last theorem combines this with an operator-MF proof of the symmetric
double.  In the intended application that proof is supplied by Shulman's
symmetric-amalgamation theorem applied to the profinite regular completion of
the residually finite group `G`.  Neither recent literature theorem is added
as a Lean axiom: callers provide their proof terms at this explicit boundary.
-/

namespace GroupApproximation

open Filter

variable {G : Type} [Group G]

/-- The precise permutation-ultraproduct centralizer conclusion used from
Kun--Thom.  It is deliberately a property of the inclusion, rather than a
theorem-shaped implication from informal words such as "Kazhdan" or
"infranormal".

Only ultraproducts indexed by `ℕ` are quantified over.  This is sufficient for
countable groups because the local definition of soficity is converted in the
proof below to a sequential sofic approximation. -/
def HasSoficCentralizerNormalization (Γ : Subgroup G) : Prop :=
  ∀ (𝒰 : Ultrafilter ℕ) (X : ℕ → FiniteModel)
      (ρ : G →* UniversalSofic 𝒰 X),
    Function.Injective ρ →
      ∀ q : UniversalSofic 𝒰 X,
        (∀ γ : G, γ ∈ Γ → Commute q (ρ γ)) →
          ∀ g γ : G, γ ∈ Γ →
            Commute (ρ g * q * (ρ g)⁻¹) (ρ γ)

/-- **Kun--Thom free-lamp obstruction.**  Centralizer normalization, together
with one element of `Γ` moved outside `Γ` by `t⁻¹ · t`, makes every free-lamp
amalgam with a nontrivial lamp nonsofic.

The proof constructs a faithful permutation-ultraproduct representation from
a hypothetical sofic approximation.  The lamp centralizes `Γ`; normalization
therefore makes its `t`-conjugate centralize `γ`, killing the Bass--Serre
witness that was proved nontrivial in `FreeLampReduction`. -/
theorem not_isSofic_freeLamp_of_centralizerNormalization
    [Countable G] (Γ : Subgroup G)
    (hcentralizer : HasSoficCentralizerNormalization Γ)
    {K : Type} [Group K] [Countable K]
    {t γ : G} (hγ : γ ∈ Γ) (hesc : t⁻¹ * γ * t ∉ Γ)
    {k : K} (hk : k ≠ 1) :
    ¬ IsSofic (FreeLamp G Γ K) := by
  intro hsofic
  obtain ⟨S⟩ :=
    (isSofic_iff_nonempty_soficApproximation (FreeLamp G Γ K)).mp hsofic
  let 𝒰 : Ultrafilter ℕ := Ultrafilter.of Filter.cofinite
  have h𝒰 : (𝒰 : Filter ℕ) ≤ Filter.cofinite := Ultrafilter.of_le _
  obtain ⟨ι, hι⟩ := exists_soficEmbedding_of_soficApproximation S h𝒰
  let ρ : G →* UniversalSofic 𝒰 S.model :=
    ι.comp (inAmbient G Γ K)
  have hρ : Function.Injective ρ :=
    hι.comp (inAmbient_injective G Γ K)
  let q : UniversalSofic 𝒰 S.model := ι (inLamp G Γ K k)
  have hq : ∀ δ : G, δ ∈ Γ → Commute q (ρ δ) := by
    intro δ hδ
    exact (inLamp_commute_inAmbient G Γ K k hδ).map ι
  have hcomm : Commute (ρ t * q * (ρ t)⁻¹) (ρ γ) :=
    hcentralizer 𝒰 S.model ρ hρ q hq t γ hγ
  have hw : ι (lampWitness G Γ K t γ k) = 1 := by
    simp only [lampWitness, map_mul, map_inv]
    change (ρ t * q * (ρ t)⁻¹) * ρ γ *
      (ρ t * q * (ρ t)⁻¹)⁻¹ * (ρ γ)⁻¹ = 1
    rw [hcomm.mul_inv_cancel, mul_inv_cancel]
  have hword : lampWitness G Γ K t γ k = 1 :=
    hι (by simpa using hw)
  exact lampWitness_ne_one G Γ K hesc hk hword

/-- The order-two lamp is nontrivial. -/
theorem flipC2_swap_ne_one : (FlipC2.swap : FlipC2) ≠ 1 := by
  decide

/-- **Kun--Thom symmetric-double obstruction.**  A strict compressor and the
permutation-ultraproduct centralizer theorem make `G *_Γ G` nonsofic.

The free-lamp obstruction is applied to `C₂`; the already formalized
isomorphism

`G *_Γ (Γ × C₂) ≅ (G *_Γ G) ⋊ C₂`

then transfers nonsoficity back to the double. -/
theorem not_isSofic_symmetricDouble_of_centralizerNormalization
    [Countable G] (Γ : Subgroup G)
    (hcentralizer : HasSoficCentralizerNormalization Γ)
    {t γ : G} (hγ : γ ∈ Γ) (hesc : t⁻¹ * γ * t ∉ Γ) :
    ¬ IsSofic (SymmetricDouble G Γ) := by
  apply not_isSofic_symmetricDouble_of_not_isSofic_freeLamp_flip G Γ
  exact not_isSofic_freeLamp_of_centralizerNormalization Γ hcentralizer
    hγ hesc flipC2_swap_ne_one

/-- The clean formal endpoint: an operator-MF symmetric double satisfying the
Kun--Thom centralizer-normalization and strict-compressor hypotheses is MF and
nonsofic.

For the explicit polynomial/Laurent elementary-group pair, Shulman's theorem
supplies `hMF`, while Kun--Thom supply `hcentralizer`, `t`, `γ`, `hγ`, and
`hesc`. -/
theorem symmetricDouble_isGroupTheoreticMF_and_not_isSofic
    [Countable G] (Γ : Subgroup G)
    (hMF : IsGroupTheoreticMF (SymmetricDouble G Γ))
    (hcentralizer : HasSoficCentralizerNormalization Γ)
    {t γ : G} (hγ : γ ∈ Γ) (hesc : t⁻¹ * γ * t ∉ Γ) :
    IsGroupTheoreticMF (SymmetricDouble G Γ) ∧
      ¬ IsSofic (SymmetricDouble G Γ) :=
  ⟨hMF, not_isSofic_symmetricDouble_of_centralizerNormalization
    Γ hcentralizer hγ hesc⟩

/-- Proof-carrying boundary for the two recent literature inputs.  An
inhabitant consists only of the exact conclusions consumed by the formal
argument: Shulman's operator-MF conclusion, Kun--Thom centralizer
normalization, and one strict witness. -/
structure KunThomShulmanDoubleData (G : Type) [Group G]
    (Γ : Subgroup G) where
  operatorMF : IsGroupTheoreticMF (SymmetricDouble G Γ)
  centralizerNormalization : HasSoficCentralizerNormalization Γ
  t : G
  γ : G
  γ_mem : γ ∈ Γ
  escapes : t⁻¹ * γ * t ∉ Γ

namespace KunThomShulmanDoubleData

/-- Every supplied Kun--Thom--Shulman datum produces the claimed separation
on its literal symmetric double. -/
theorem conclusion [Countable G] {Γ : Subgroup G}
    (D : KunThomShulmanDoubleData G Γ) :
    IsGroupTheoreticMF (SymmetricDouble G Γ) ∧
      ¬ IsSofic (SymmetricDouble G Γ) :=
  symmetricDouble_isGroupTheoreticMF_and_not_isSofic Γ D.operatorMF
    D.centralizerNormalization D.γ_mem D.escapes

/-- Existence form of the endpoint, once the explicit literature datum has
been supplied. -/
theorem exists_groupTheoreticMF_not_sofic [Countable G] {Γ : Subgroup G}
    (D : KunThomShulmanDoubleData G Γ) :
    ∃ (E : Type) (_ : Group E), Countable E ∧
      IsGroupTheoreticMF E ∧ ¬ IsSofic E :=
  ⟨SymmetricDouble G Γ, inferInstance, inferInstance,
    D.conclusion.1, D.conclusion.2⟩

end KunThomShulmanDoubleData

end GroupApproximation
