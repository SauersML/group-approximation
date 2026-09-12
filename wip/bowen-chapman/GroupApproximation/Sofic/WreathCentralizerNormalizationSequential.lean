import GroupApproximation.KunThom.NormalizationFromCriterion
import GroupApproximation.Sofic.WreathCentralizerNormalization

/-!
# Coset wreath products under sequential centralizer normalization

The asymptotic form of `Sofic/WreathCentralizerNormalization`.  The hypothesis
is `HasSequentialCentralizerNormalization Γ`: along every sofic approximation
of `G`, a sequence of permutations that almost commutes with each element of
`Γ` has `g`-conjugates that almost commute with each element of `Γ`.

The proof restricts a sofic approximation of `W = K ≀_{G/Γ} G` to `G` and feeds
it the images of a nontrivial one-site lamp at the base coset.  These almost
commute with `Γ` because the lamp commutes exactly with `Γ` in `W`.  The
conclusion at `t` says that the permutations assigned to the commutator of the
`t`-conjugated lamp with `γ` approach the identity.  Asymptotic faithfulness
then forces that commutator to be trivial in `W`, and
`wreath_conj_lamp_not_commute` shows it is not when `t⁻¹ γ t ∉ Γ`.
-/

namespace GroupApproximation

open SemidirectProduct

/-- **Coset wreath products over a sequentially normalizing pair are not
sofic.** -/
theorem not_isSofic_wreath_of_sequentialNormalization_of_ne_one
    {G : Type} [Group G] [Countable G] (Γ : Subgroup G)
    (hcentralizer : HasSequentialCentralizerNormalization Γ)
    {K : Type} [Group K] [Countable K] {k : K} (hk : k ≠ 1)
    {t γ : G} (hγ : γ ∈ Γ) (hesc : t⁻¹ * γ * t ∉ Γ) :
    ¬ IsSofic (Wreath K G (G ⧸ Γ)) := by
  classical
  intro hsofic
  haveI : Countable (G ⧸ Γ) := QuotientGroup.mk_surjective.countable
  obtain ⟨S⟩ :=
    (isSofic_iff_nonempty_soficApproximation (Wreath K G (G ⧸ Γ))).mp hsofic
  let lamp : Wreath K G (G ⧸ Γ) := inl (Lamp.single (wreathBaseCoset Γ) k)
  have hv : ∀ δ ∈ Γ,
      (S.comap (inr : G →* Wreath K G (G ⧸ Γ)) inr_injective).AlmostCommutes
        (fun n ↦ S.map n lamp) δ := by
    intro δ hδ
    exact S.almostCommutes_comap_of_commute (inr : G →* Wreath K G (G ⧸ Γ))
      inr_injective
      (wreath_commute_inl_single_inr ((smul_wreathBaseCoset_eq_iff Γ δ).mpr hδ) k)
  have hconj := hcentralizer
    (S.comap (inr : G →* Wreath K G (G ⧸ Γ)) inr_injective)
    (fun n ↦ S.map n lamp) hv t γ hγ
  have hconj' : Vanishing fun n ↦ hammingDistance (S.model n)
      (S.map n (inr t) * S.map n lamp * (S.map n (inr t))⁻¹ * S.map n (inr γ))
      (S.map n (inr γ) * (S.map n (inr t) * S.map n lamp * (S.map n (inr t))⁻¹)) :=
    hconj
  have hsum := S.hamming_conj_commute_vanishing (inr t) lamp (inr γ) hconj'
  exact S.not_hamming_vanishing_of_ne (wreath_conj_lamp_not_commute Γ hk hesc) hsum

/-- **The order-two lamp**, under sequential centralizer normalization. -/
theorem not_isSofic_wreath_of_sequentialNormalization
    {G : Type} [Group G] [Countable G] (Γ : Subgroup G)
    (hcentralizer : HasSequentialCentralizerNormalization Γ)
    {t γ : G} (hγ : γ ∈ Γ) (hesc : t⁻¹ * γ * t ∉ Γ) :
    ¬ IsSofic (Wreath (Multiplicative (ZMod 2)) G (G ⧸ Γ)) :=
  not_isSofic_wreath_of_sequentialNormalization_of_ne_one Γ hcentralizer
    (k := Multiplicative.ofAdd (1 : ZMod 2))
    (by rw [Ne, ofAdd_eq_one]; decide) hγ hesc

end GroupApproximation
