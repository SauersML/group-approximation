import GroupApproximation.Sofic.SplitExtensionEndpoint
import GroupApproximation.Sofic.LiteralDoublingWreathNonMF
import GroupApproximation.Monsters.ExplicitLinearModelScaling
import GroupApproximation.Leavitt.GeneralCornerTheorem
import GroupApproximation.Algebra.LampCountable
import GroupApproximation.Kazhdan.KazhdanUniverse
import GroupApproximation.Meta.AxiomGuard

/-!
# Related work: Eckhardt's generalized wreath products are not MF

The census row `a494a9e94d28` is the related-work sentence of
`non_mf_groups_exist.tex`, lines 354--356:

> Eckhardt's note~\cite{Eckhardt} gives a short, elementary proof that certain
> generalized wreath products are not MF\@.

with `\bibitem[Ec]{Eckhardt}` = C. Eckhardt, *Non-MF groups and non-finite full
group C*-algebras*, preprint 2026, arXiv:2608.28772 (tex lines 2350--2354).

## Which groups

The groups of the note are the generalized (permutational) wreath products
`W = (⊕_{G/Γ} ℤ/2) ⋊ G`, where `Γ` has property (T), `β : Γ → Γ` is injective
and not surjective, and `G = ⟨Γ, t | t γ t⁻¹ = β γ⟩` is the ascending HNN
extension acting on its coset space `G/Γ`. In the corpus:

* `G` is `MarkedCompression.Vertical β hβ` (mapping telescope ⋊ ℤ). It contains
  `Γ` injectively (`MarkedCompression.iotaVertical_injective`), and the stable
  letter satisfies the HNN relation (`MarkedCompression.vertical_compress`).
  `MarkedCompression.verticalLift` gives the universal property;
* `G/Γ` is `MarkedCompression.Cosets β hβ`;
* `W` is `MarkedCompression.WreathV (K := ℤ/2) β hβ`, named `EckhardtW` below.

## Proof route (reused, not reproved)

This is the configuration of tex lines 336--339 (a Kazhdan subgroup `L`
conjugated into itself by `u`, and an element `c` commuting with `L` whose
conjugate `u c u⁻¹` does not commute with `L`):

* `L` is the base copy of `Γ`;
* `u = t`;
* `c` is the one-site involutive lamp at the site `t Γ`.

The compressed copy `t Γ t⁻¹` fixes `t Γ`, so it commutes with the lamp there.
Any `a₀ ∉ range β` moves that site, so the commutator is nontrivial. The corpus
theorem `MarkedCompression.not_isCDEOperatorMF_wreath` feeds this involutive
compression witness to `ProjectionCompressionCollapse`, the projection-collapse
form of the one-sided compression criterion (Kazhdan projection in the norm
matrix corona). That criterion shows `W` is not MF.

The current printed Theorem `thm:compression-criterion` is stated through a
normal Kazhdan defect subgroup. That hypothesis is not what the corpus route
uses for `W`: it uses the involutive projection-collapse variant, whose inputs
are only the hypotheses printed above.

What this module adds is bookkeeping:

* non-surjectivity gives a mover `a₀`;
* property (T) gives countability of `Γ`, hence of `W`;
* the textbook (T) is converted to the real Kazhdan pair;
* a concrete infinite family: the affine Kazhdan base `gammaBar` with the
  scaling self-embeddings `conjScale m`, `m ≥ 2`. The corpus's literal doubling
  wreath product `LiteralDoublingWreath.W` is `EckhardtW conjD _` by `rfl`.

The endpoints carry only printed hypotheses. No `Statement` gap remains.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace RelatedEckhardt

universe w

/-- Eckhardt's generalized wreath product: mod-two lamps over the coset space
`G/Γ` of the ascending HNN extension `G` of `Γ` along `β`, acted on by `G`. -/
abbrev EckhardtW {Γ : Type} [Group Γ] (β : Γ →* Γ) (hβ : Function.Injective β) :
    Type :=
  MarkedCompression.WreathV (K := LiteralDoublingWreath.C2) β hβ

/-- A non-surjective map misses some point. -/
theorem exists_not_mem_range_of_not_surjective {X Y : Type*} {f : X → Y}
    (hf : ¬ Function.Surjective f) : ∃ b : Y, b ∉ Set.range f := by
  by_contra h
  apply hf
  intro b
  by_contra hb
  exact h ⟨b, fun hb' => hb (Set.mem_range.mp hb')⟩

/-- Property (T) makes `Γ` finitely generated, hence countable, and so the
wreath product is countable. -/
theorem eckhardtW_countable {Γ : Type} [Group Γ] (β : Γ →* Γ)
    (hβ : Function.Injective β) (hΓ : HasKazhdanPropertyT.{0, 0} Γ) :
    Countable (EckhardtW β hβ) := by
  haveI : Countable Γ := GeneralCornerTheorem.countable_of_hasKazhdanPropertyT hΓ
  infer_instance

/-- **Eckhardt's groups are not MF (operator-MF form).** -/
theorem eckhardtW_not_isOperatorMF {Γ : Type} [Group Γ]
    (hΓ : HasKazhdanPropertyT.{0, 0} Γ) (β : Γ →* Γ) (hβ : Function.Injective β)
    (hns : ¬ Function.Surjective β) :
    ¬ IsOperatorMF (EckhardtW β hβ) := by
  classical
  haveI : Countable (EckhardtW β hβ) := eckhardtW_countable β hβ hΓ
  obtain ⟨a₀, ha₀⟩ := exists_not_mem_range_of_not_surjective hns
  exact MarkedCompression.not_isOperatorMF_wreath (K₀ := LiteralDoublingWreath.C2)
    β hβ hΓ LiteralDoublingWreath.c_ne_one LiteralDoublingWreath.c_mul_self ha₀

/-- **Eckhardt's groups are not MF (literal CDE form).** -/
theorem eckhardtW_not_isCDEOperatorMF {Γ : Type} [Group Γ]
    (hΓ : HasKazhdanPropertyT.{0, 0} Γ) (β : Γ →* Γ) (hβ : Function.Injective β)
    (hns : ¬ Function.Surjective β) :
    ¬ @IsCDEOperatorMF (EckhardtW β hβ) _ (eckhardtW_countable β hβ hΓ) := by
  classical
  haveI : Countable (EckhardtW β hβ) := eckhardtW_countable β hβ hΓ
  obtain ⟨a₀, ha₀⟩ := exists_not_mem_range_of_not_surjective hns
  exact MarkedCompression.not_isCDEOperatorMF_wreath (K₀ := LiteralDoublingWreath.C2)
    β hβ hΓ LiteralDoublingWreath.c_ne_one LiteralDoublingWreath.c_mul_self ha₀

/-- The corpus's literal doubling wreath product is the member of the family at
the affine doubling embedding. -/
theorem literalDoublingW_eq_eckhardtW :
    LiteralDoublingWreath.W =
      EckhardtW ExplicitLinearModel.conjD ExplicitLinearModel.conjD_injective :=
  rfl

/-! ## A concrete infinite family -/

theorem scale_ne_zero {m : ℕ} (hm : 2 ≤ m) : m ≠ 0 := by
  omega

/-- The scaling self-embedding of the affine Kazhdan base is proper. -/
theorem scale_not_surjective {m : ℕ} (hm : 2 ≤ m) :
    ¬ Function.Surjective
      (ExplicitLinearModelScaling.conjScale m (scale_ne_zero hm)) := fun h =>
  ExplicitLinearModelScaling.v1G_not_mem_range_conjScale (scale_ne_zero hm) hm
    (Set.mem_range.mpr (h _))

/-- **The explicit family.** For every `m ≥ 2`, the generalized wreath product
over the ascending HNN extension of `gammaBar` along `conjScale m` is not MF. -/
theorem scaleFamily_not_isOperatorMF {m : ℕ} (hm : 2 ≤ m) :
    ¬ IsOperatorMF
      (EckhardtW (ExplicitLinearModelScaling.conjScale m (scale_ne_zero hm))
        (ExplicitLinearModelScaling.conjScale_injective (scale_ne_zero hm))) :=
  eckhardtW_not_isOperatorMF CommutingLampCollapse.gammaBar_hasKazhdanPropertyT
    _ _ (scale_not_surjective hm)

/-! ## The sentence -/

/-- **Tex lines 354--356.** Closed form of the related-work sentence.

1. For every group `Γ` with textbook property (T) and every injective,
   non-surjective `β : Γ →* Γ`:
   * the acting group is the ascending HNN extension (`Γ` embeds and
     `t γ t⁻¹ = β γ`);
   * the generalized wreath product `(⊕_{G/Γ} ℤ/2) ⋊ G` is not MF, both in the
     operator-MF form and in the literal CDE form.
2. The hypotheses are met by an explicit infinite family: `gammaBar` has
   (T), and for every `m ≥ 2` the embedding `conjScale m` is proper and its
   wreath product is not MF. -/
theorem manuscriptSentence_eckhardtGeneralizedWreathNotMF :
    (∀ (Γ : Type) [Group Γ] (hΓ : HasKazhdanPropertyTComplex.{0, w} Γ)
        (β : Γ →* Γ) (hβ : Function.Injective β), ¬ Function.Surjective β →
      (Function.Injective (MarkedCompression.iotaVertical β hβ) ∧
        ∀ γ : Γ, MarkedCompression.tVertical β hβ *
            MarkedCompression.iotaVertical β hβ γ *
              (MarkedCompression.tVertical β hβ)⁻¹ =
            MarkedCompression.iotaVertical β hβ (β γ)) ∧
      ¬ IsOperatorMF (EckhardtW β hβ) ∧
      ¬ @IsCDEOperatorMF (EckhardtW β hβ) _
          (eckhardtW_countable β hβ
            ((hasKazhdanPropertyT_iff_textbook.{0, w}).mpr hΓ))) ∧
    (HasKazhdanPropertyTComplex.{0, w} ExplicitLinearModel.gammaBar ∧
      ∀ (m : ℕ) (hm : 2 ≤ m),
        ¬ Function.Surjective
            (ExplicitLinearModelScaling.conjScale m (scale_ne_zero hm)) ∧
        ¬ IsOperatorMF
          (EckhardtW (ExplicitLinearModelScaling.conjScale m (scale_ne_zero hm))
            (ExplicitLinearModelScaling.conjScale_injective (scale_ne_zero hm)))) := by
  refine ⟨?_, ?_⟩
  · intro Γ _ hΓ β hβ hns
    have hΓ' : HasKazhdanPropertyT.{0, 0} Γ :=
      (hasKazhdanPropertyT_iff_textbook.{0, w}).mpr hΓ
    exact ⟨⟨MarkedCompression.iotaVertical_injective β hβ,
        MarkedCompression.vertical_compress β hβ⟩,
      eckhardtW_not_isOperatorMF hΓ' β hβ hns,
      eckhardtW_not_isCDEOperatorMF hΓ' β hβ hns⟩
  · exact ⟨(hasKazhdanPropertyT_iff_textbook.{0, w}).mp
        CommutingLampCollapse.gammaBar_hasKazhdanPropertyT,
      fun _ hm => ⟨scale_not_surjective hm, scaleFamily_not_isOperatorMF hm⟩⟩

end RelatedEckhardt
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.RelatedEckhardt.EckhardtW
#audit_axioms GroupApproximation.Manuscript.NonMF.RelatedEckhardt.exists_not_mem_range_of_not_surjective
#audit_axioms GroupApproximation.Manuscript.NonMF.RelatedEckhardt.eckhardtW_countable
#audit_axioms GroupApproximation.Manuscript.NonMF.RelatedEckhardt.eckhardtW_not_isOperatorMF
#audit_axioms GroupApproximation.Manuscript.NonMF.RelatedEckhardt.eckhardtW_not_isCDEOperatorMF
#audit_axioms GroupApproximation.Manuscript.NonMF.RelatedEckhardt.literalDoublingW_eq_eckhardtW
#audit_axioms GroupApproximation.Manuscript.NonMF.RelatedEckhardt.scale_ne_zero
#audit_axioms GroupApproximation.Manuscript.NonMF.RelatedEckhardt.scale_not_surjective
#audit_axioms GroupApproximation.Manuscript.NonMF.RelatedEckhardt.scaleFamily_not_isOperatorMF
#audit_closed_axioms GroupApproximation.Manuscript.NonMF.RelatedEckhardt.manuscriptSentence_eckhardtGeneralizedWreathNotMF
