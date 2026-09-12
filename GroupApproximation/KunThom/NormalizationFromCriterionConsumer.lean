import GroupApproximation.KunThom.NormalizationFromCriterion
import GroupApproximation.Sofic.MFNonsoficDoubleEndpoint

/-!
# Nonsofic free-lamp amalgams and symmetric doubles from sequential normalization

These are the consumers of `HasSequentialCentralizerNormalization`, the
sequential form of Kun--Thom's Theorem 4.1.  They have the same hypotheses as
`not_isSofic_freeLamp_of_centralizerNormalization` and
`not_isSofic_symmetricDouble_of_centralizerNormalization`, with the sequential
normalization statement in place of the ultraproduct one, and they use no
ultraproduct.

The argument: restrict a sofic approximation `S` of the amalgam
`G *_Γ (Γ × K)` to `G`, and take for `v` the model permutations of a
nontrivial lamp `k`.  The lamp commutes with `Γ` in the amalgam, so `v` almost
commutes with every `A(γ)`, `γ ∈ Γ`.  Normalization makes `A(t) v A(t)⁻¹`
almost commute with `A(γ)`.  Approximate multiplicativity then makes the model
permutations of `t k t⁻¹ γ` and `γ t k t⁻¹` asymptotically equal, while the
escape `t⁻¹ γ t ∉ Γ` makes these two group elements distinct
(`lampWitness_ne_one`).  Asymptotic faithfulness separates distinct elements,
which is the contradiction.
-/

namespace GroupApproximation

variable {G : Type} [Group G]

/-- **Kun--Thom free-lamp obstruction, sequential form.** -/
theorem not_isSofic_freeLamp_of_sequentialNormalization
    [Countable G] (Γ : Subgroup G)
    (hcentralizer : HasSequentialCentralizerNormalization Γ)
    {K : Type} [Group K] [Countable K]
    {t γ : G} (hγ : γ ∈ Γ) (hesc : t⁻¹ * γ * t ∉ Γ)
    {k : K} (hk : k ≠ 1) :
    ¬ IsSofic (FreeLamp G Γ K) := by
  intro hsofic
  obtain ⟨S⟩ :=
    (isSofic_iff_nonempty_soficApproximation (FreeLamp G Γ K)).mp hsofic
  have hv : ∀ δ ∈ Γ,
      (S.comap (inAmbient G Γ K) (inAmbient_injective G Γ K)).AlmostCommutes
        (fun n ↦ S.map n (inLamp G Γ K k)) δ := fun δ hδ ↦
    S.almostCommutes_comap_of_commute (inAmbient G Γ K) (inAmbient_injective G Γ K)
      (inLamp_commute_inAmbient G Γ K k hδ)
  have hconj := hcentralizer
    (S.comap (inAmbient G Γ K) (inAmbient_injective G Γ K))
    (fun n ↦ S.map n (inLamp G Γ K k)) hv t γ hγ
  have hconj' : Vanishing fun n ↦ hammingDistance (S.model n)
      (S.map n (inAmbient G Γ K t) * S.map n (inLamp G Γ K k) *
          (S.map n (inAmbient G Γ K t))⁻¹ * S.map n (inAmbient G Γ K γ))
      (S.map n (inAmbient G Γ K γ) *
        (S.map n (inAmbient G Γ K t) * S.map n (inLamp G Γ K k) *
          (S.map n (inAmbient G Γ K t))⁻¹)) :=
    hconj
  have hsum := S.hamming_conj_commute_vanishing (inAmbient G Γ K t)
    (inLamp G Γ K k) (inAmbient G Γ K γ) hconj'
  have hne : inAmbient G Γ K t * inLamp G Γ K k * (inAmbient G Γ K t)⁻¹ *
        inAmbient G Γ K γ ≠
      inAmbient G Γ K γ *
        (inAmbient G Γ K t * inLamp G Γ K k * (inAmbient G Γ K t)⁻¹) := by
    intro heq
    apply lampWitness_ne_one G Γ K hesc hk
    unfold lampWitness
    rw [heq]
    group
  exact S.not_hamming_vanishing_of_ne hne hsum

/-- **Kun--Thom symmetric-double obstruction, sequential form.**  A strict
compressor witness and sequential centralizer normalization make `G *_Γ G`
nonsofic.  The signature matches
`not_isSofic_symmetricDouble_of_centralizerNormalization` apart from the
normalization hypothesis. -/
theorem not_isSofic_symmetricDouble_of_sequentialNormalization
    [Countable G] (Γ : Subgroup G)
    (hcentralizer : HasSequentialCentralizerNormalization Γ)
    {t γ : G} (hγ : γ ∈ Γ) (hesc : t⁻¹ * γ * t ∉ Γ) :
    ¬ IsSofic (SymmetricDouble G Γ) := by
  apply not_isSofic_symmetricDouble_of_not_isSofic_freeLamp_flip G Γ
  exact not_isSofic_freeLamp_of_sequentialNormalization Γ hcentralizer
    hγ hesc flipC2_swap_ne_one

end GroupApproximation
