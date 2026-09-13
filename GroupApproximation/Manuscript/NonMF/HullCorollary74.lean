import GroupApproximation.GGT.HullSCFreeProductFactor
import GroupApproximation.GGT.HullSCLemma51EmbeddedBridgeHolds
import GroupApproximation.Manuscript.NonMF.HullBallForm
import GroupApproximation.Manuscript.NonMF.HullCorollary73
import GroupApproximation.Manuscript.NonMF.HullFreeFactorSuitable
import GroupApproximation.Manuscript.NonMF.HullLemma510
import GroupApproximation.Manuscript.NonMF.Saturation
import GroupApproximation.Meta.AxiomGuard

/-!
# Hull, Corollary 7.4

M. Hull, *Small cancellation in acylindrically hyperbolic groups*, arXiv:1308.4345, §7.
`non_mf_groups_exist.tex` cites this corollary at tex line 1682.

> **Corollary 7.4.** Let `G₁, G₂ ∈ AH` with `G₁` finitely generated, `G₂` countable.  Then there
> exists a non-virtually cyclic group `Q` and surjective homomorphisms `αᵢ : Gᵢ → Q` for
> `i = 1, 2`.  In addition, if `G₂` is finitely generated, then we can choose `Q ∈ AH₀`, and if
> `K(Gᵢ) = {1}`, then for any finite subset `Fᵢ ⊂ Gᵢ`, we can choose `αᵢ` to be injective on
> `Fᵢ`.

`G ∈ AH` is `IsAcylindricallyHyperbolic G`, `K(G) = {1}` is `HasTrivialFiniteRadical G`, and
`AH₀` is `HullFiniteRadical.IsAH0`.  `PrintedHullCorollary74` quantifies `F₁` and `F₂` before
the quotient, so one choice of `Q, α₁, α₂` meets every clause at once.

`TorsionFreePrinted.HullCommonQuotientPrinted` is the special case the proof of
`cor:relative-quotient` uses (both groups finitely presented and torsion-free), proved in
`GGT/HullSCCommonQuotientPrinted.lean`.  This module proves the printed statement.

## The proof

* Replace `Gᵢ` by `Gᵢ / K(Gᵢ)`, which lies in `AH₀` by Lemma 5.10
  (`HullLemma510.printedHullLemma510`).  When `K(Gᵢ) = {1}` the quotient map is injective, so
  injectivity on `Fᵢ` passes back.
* For `E, H ∈ AH₀`, let `Γ = E ∗ H` over the union of Hull alphabets of `E` and `H`.  Both
  factors are suitable (`HullFreeFactorSuitable.suitable_range_inl`, `suitable_range_inr`).
* Theorem 7.1 at `Γ`, along the image of `H`, with the generators of `E` as targets and the image
  of `E` as the prescribed suitable family, gives `q₁ : Γ → Q₁`.  The image of `E` lies in the
  image of `H`, so `Q₁` is a quotient of `H`.  So `Q₁` is countable, and finitely generated when
  `H` is.  The image of `E` stays suitable (`HullStep.suitable_map_family`).
* If `H` is finitely generated, apply Theorem 7.1 at `Q₁`, along the image of `E`, with a finite
  generating family of `Q₁` as targets.  The result `Q₂` has a Hull alphabet, so it lies in `AH`,
  and it contains a suitable subgroup, so `K(Q₂) = {1}`.
* Otherwise apply Corollary 7.3 (`HullCorollary73.printedHullCorollary73_of_tower`) at `Q₁` with
  `S` the image of `E`.
* In both cases the images of `F₁` and `F₂` lie in balls on which each quotient map is injective.

Theorem 7.1 enters as `HullSC.HullTowerStatementGeneral`.
`printedHullCorollary74_of_leastAreaLeaves` takes exactly the two least-area wall statements.
The embedded bridge is proved (`HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed`),
so `printedHullCorollary74_of_greendlinger` takes the Greendlinger wall alone.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace HullCorollary74

open GroupApproximation.WordMetric
open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.Manuscript.NonMF.TorsionFreePrinted
open GroupApproximation.Manuscript.NonMF.HullFiniteRadical

universe u

/-- A finitely generated group has a finite generating family `t₁, …, t_m`. -/
theorem exists_fin_generating_family (G : Type u) [Group G] (hG : Group.FG G) :
    ∃ (m : ℕ) (t : Fin m → G), Subgroup.closure (Set.range t) = ⊤ := by
  obtain ⟨_, S, -, hS⟩ := Group.fg_iff'.mp hG
  refine ⟨S.card, fun i => (S.equivFin.symm i : G), ?_⟩
  have hrange : Set.range (fun i : Fin S.card => (S.equivFin.symm i : G)) = (S : Set G) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (S.equivFin.symm i).2
    · intro hx
      exact ⟨S.equivFin ⟨x, hx⟩, by simp⟩
  rw [hrange]
  exact hS

#audit_axioms exists_fin_generating_family

section CommonQuotient

variable {E H : Type} [Group E] [Group H]

/-- **Corollary 7.4 for `E, H ∈ AH₀`**, from Theorem 7.1. -/
theorem exists_commonQuotient_of_hullGeneratingSet
    (htower : HullSC.HullTowerStatementGeneral.{0})
    (A : HullGeneratingSet E) (B : HullGeneratingSet H)
    (hE : HasTrivialFiniteRadical E) (hH : HasTrivialFiniteRadical H)
    (hfgE : Group.FG E) (hcountH : Countable H) {F₁ : Set E} {F₂ : Set H}
    (hF₁ : F₁.Finite) (hF₂ : F₂.Finite) :
    ∃ (Q : Type) (_ : Group Q) (β₁ : E →* Q) (β₂ : H →* Q),
      ¬ GGT.IsVirtuallyCyclic Q ∧ Function.Surjective β₁ ∧ Function.Surjective β₂ ∧
        (Group.FG H → IsAH0 Q) ∧ Set.InjOn β₁ F₁ ∧ Set.InjOn β₂ F₂ := by
  classical
  -- `Γ = E ∗ H` over the union alphabet, with both factors suitable
  obtain ⟨C, hC⟩ := HullFreeFactorSuitable.exists_hullGeneratingSet_unionAlphabet A B
  have hsE : Suitable C.alphabet (Monoid.Coprod.inl : E →* Monoid.Coprod E H).range := by
    rw [hC]
    exact HullFreeFactorSuitable.suitable_range_inl A B hE
  have hsH : Suitable C.alphabet (Monoid.Coprod.inr : H →* Monoid.Coprod E H).range := by
    rw [hC]
    exact HullFreeFactorSuitable.suitable_range_inr A B hH
  -- a ball of `Γ(Γ, C)` containing the images of `F₁` and `F₂`
  have hΩ : (((Monoid.Coprod.inl : E →* Monoid.Coprod E H) : E → Monoid.Coprod E H) '' F₁ ∪
      ((Monoid.Coprod.inr : H →* Monoid.Coprod E H) : H → Monoid.Coprod E H) '' F₂).Finite :=
    (hF₁.image _).union (hF₂.image _)
  obtain ⟨R₁, hR₁⟩ := exists_subset_cayleyBall C.alphabet hΩ
  -- a finite generating family of `E`
  obtain ⟨m, t, htop⟩ := exists_fin_generating_family E hfgE
  -- **Theorem 7.1 at `Γ`**, along the image of `H`, absorbing the generators of `E`
  obtain ⟨D₁⟩ := htower
    (S := fun _ : Fin 1 => (Monoid.Coprod.inl : E →* Monoid.Coprod E H).range)
    C hsH (fun _ => hsE) (fun i => (Monoid.Coprod.inl (t i) : Monoid.Coprod E H)) R₁
  have hle : Subgroup.closure (Set.range t) ≤
      (((Monoid.Coprod.inr : H →* Monoid.Coprod E H).range.map D₁.step.q).comap
        D₁.step.q).comap (Monoid.Coprod.inl : E →* Monoid.Coprod E H) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact D₁.mem_map i
  have hK₁ : ((Monoid.Coprod.inr : H →* Monoid.Coprod E H).range.map D₁.step.q).comap
      D₁.step.q = ⊤ := by
    refine HullSC.eq_top_of_inl_inr_mem (fun a => ?_) (fun b => ?_)
    · have ha : a ∈ Subgroup.closure (Set.range t) := by
        rw [htop]
        exact Subgroup.mem_top a
      exact hle ha
    · show D₁.step.q (Monoid.Coprod.inr b)
        ∈ (Monoid.Coprod.inr : H →* Monoid.Coprod E H).range.map D₁.step.q
      exact Subgroup.mem_map_of_mem _ (MonoidHom.mem_range.mpr ⟨b, rfl⟩)
  -- so `Q₁` is a quotient of `H`
  have hsurj₂ : Function.Surjective
      (D₁.step.q.comp (Monoid.Coprod.inr : H →* Monoid.Coprod E H)) := by
    intro y
    obtain ⟨x, rfl⟩ := D₁.step.surjective y
    have hx : x ∈ ((Monoid.Coprod.inr : H →* Monoid.Coprod E H).range.map D₁.step.q).comap
        D₁.step.q := by
      rw [hK₁]
      exact Subgroup.mem_top x
    rw [Subgroup.mem_comap] at hx
    obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hx
    obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hz
    exact ⟨b, hzx⟩
  haveI : Countable D₁.step.Q := hsurj₂.countable
  -- the image of `E` stays suitable
  have hsE₁ : Suitable D₁.step.hullSet.alphabet
      ((Monoid.Coprod.inl : E →* Monoid.Coprod E H).range.map D₁.step.q) :=
    D₁.step.suitable_map_family 0
  -- a ball of `Γ(Q₁, 𝒜₁)` containing the images of `F₁` and `F₂`
  have hΩ₂ : ((D₁.step.q : Monoid.Coprod E H → D₁.step.Q) ''
      (((Monoid.Coprod.inl : E →* Monoid.Coprod E H) : E → Monoid.Coprod E H) '' F₁ ∪
        ((Monoid.Coprod.inr : H →* Monoid.Coprod E H) : H → Monoid.Coprod E H) '' F₂)).Finite :=
    hΩ.image _
  obtain ⟨R₂, hR₂⟩ := exists_subset_cayleyBall D₁.step.hullSet.alphabet hΩ₂
  have hball₁ : ∀ x ∈ F₁,
      (Monoid.Coprod.inl x : Monoid.Coprod E H) ∈ cayleyBall C.alphabet R₁ :=
    fun x hx => hR₁ (Set.mem_union_left _ (Set.mem_image_of_mem _ hx))
  have hball₂ : ∀ x ∈ F₂,
      (Monoid.Coprod.inr x : Monoid.Coprod E H) ∈ cayleyBall C.alphabet R₁ :=
    fun x hx => hR₁ (Set.mem_union_right _ (Set.mem_image_of_mem _ hx))
  have hball₁' : ∀ x ∈ F₁, D₁.step.q (Monoid.Coprod.inl x : Monoid.Coprod E H)
      ∈ cayleyBall D₁.step.hullSet.alphabet R₂ :=
    fun x hx => hR₂ (Set.mem_image_of_mem _ (Set.mem_union_left _ (Set.mem_image_of_mem _ hx)))
  have hball₂' : ∀ x ∈ F₂, D₁.step.q (Monoid.Coprod.inr x : Monoid.Coprod E H)
      ∈ cayleyBall D₁.step.hullSet.alphabet R₂ :=
    fun x hx => hR₂ (Set.mem_image_of_mem _ (Set.mem_union_right _ (Set.mem_image_of_mem _ hx)))
  have hinj₁ : ∀ x ∈ F₁, ∀ y ∈ F₁, D₁.step.q (Monoid.Coprod.inl x : Monoid.Coprod E H)
      = D₁.step.q (Monoid.Coprod.inl y : Monoid.Coprod E H) → x = y :=
    fun x hx y hy h => Monoid.Coprod.inl_injective (D₁.step.injOn (hball₁ x hx) (hball₁ y hy) h)
  have hinj₂ : ∀ x ∈ F₂, ∀ y ∈ F₂, D₁.step.q (Monoid.Coprod.inr x : Monoid.Coprod E H)
      = D₁.step.q (Monoid.Coprod.inr y : Monoid.Coprod E H) → x = y :=
    fun x hx y hy h => Monoid.Coprod.inr_injective (D₁.step.injOn (hball₂ x hx) (hball₂ y hy) h)
  by_cases hfgH : Group.FG H
  · -- **Theorem 7.1 at `Q₁`**, along the image of `E`, absorbing a generating family of `Q₁`
    haveI := hfgH
    obtain ⟨m₂, t₂, htop₂⟩ :=
      exists_fin_generating_family D₁.step.Q (Group.fg_of_surjective hsurj₂)
    obtain ⟨D₂⟩ := htower (S := fun j : Fin 0 => Fin.elim0 j) D₁.step.hullSet hsE₁
      (fun j : Fin 0 => Fin.elim0 j) t₂ R₂
    have hEtop : ((Monoid.Coprod.inl : E →* Monoid.Coprod E H).range.map D₁.step.q).map
        D₂.step.q = ⊤ :=
      map_eq_top_of_generators_mem D₂.step.q D₂.step.surjective htop₂ D₂.mem_map
    haveI hQ₂ah : IsAcylindricallyHyperbolic D₂.step.Q :=
      HullSC.isAcylindricallyHyperbolic_of_hullGeneratingSet D₂.step.hullSet
    refine ⟨D₂.step.Q, D₂.step.group,
      D₂.step.q.comp (D₁.step.q.comp (Monoid.Coprod.inl : E →* Monoid.Coprod E H)),
      D₂.step.q.comp (D₁.step.q.comp (Monoid.Coprod.inr : H →* Monoid.Coprod E H)),
      HullSC.not_isVirtuallyCyclic_of_actsNonElementarily
        (isIsometricAction_cayley D₂.step.hullSet.alphabet) D₂.step.hullSet.nonElementary,
      ?_, ?_,
      fun _ => ⟨hQ₂ah, hasTrivialFiniteRadical_iff_finiteRadical_eq_bot.mpr
        (finiteRadical_eq_bot_of_suitable D₂.step.suitable_map)⟩, ?_, ?_⟩
    · intro y
      have hy : y ∈ ((Monoid.Coprod.inl : E →* Monoid.Coprod E H).range.map D₁.step.q).map
          D₂.step.q := by
        rw [hEtop]
        exact Subgroup.mem_top y
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
      obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hw
      exact ⟨a, rfl⟩
    · intro y
      obtain ⟨x, rfl⟩ := D₂.step.surjective y
      obtain ⟨b, hb⟩ := hsurj₂ x
      exact ⟨b, by rw [MonoidHom.comp_apply, hb]⟩
    · intro x hx y hy hxy
      exact hinj₁ x hx y hy (D₂.step.injOn (hball₁' x hx) (hball₁' y hy) hxy)
    · intro x hx y hy hxy
      exact hinj₂ x hx y hy (D₂.step.injOn (hball₂' x hx) (hball₂' y hy) hxy)
  · -- **Corollary 7.3 at `Q₁`**, with `S` the image of `E`
    obtain ⟨Q, instQ, η, hnvc, hηsurj, hηS, hηinj⟩ :=
      HullCorollary73.printedHullCorollary73_of_tower htower D₁.step.hullSet hsE₁ R₂
    refine ⟨Q, instQ, η.comp (D₁.step.q.comp (Monoid.Coprod.inl : E →* Monoid.Coprod E H)),
      η.comp (D₁.step.q.comp (Monoid.Coprod.inr : H →* Monoid.Coprod E H)), hnvc, ?_, ?_,
      fun h => absurd h hfgH, ?_, ?_⟩
    · intro y
      obtain ⟨s, hs, rfl⟩ := hηS y
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hs
      obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hw
      exact ⟨a, rfl⟩
    · intro y
      obtain ⟨x, rfl⟩ := hηsurj y
      obtain ⟨b, hb⟩ := hsurj₂ x
      exact ⟨b, by rw [MonoidHom.comp_apply, hb]⟩
    · intro x hx y hy hxy
      exact hinj₁ x hx y hy (hηinj (hball₁' x hx) (hball₁' y hy) hxy)
    · intro x hx y hy hxy
      exact hinj₂ x hx y hy (hηinj (hball₂' x hx) (hball₂' y hy) hxy)

#audit_axioms exists_commonQuotient_of_hullGeneratingSet

end CommonQuotient

/-! ## The printed corollary -/

/-- **Hull, Corollary 7.4.**  *"Let `G₁, G₂ ∈ AH` with `G₁` finitely generated, `G₂` countable.
Then there exists a non-virtually cyclic group `Q` and surjective homomorphisms `αᵢ : Gᵢ → Q` for
`i = 1, 2`. In addition, if `G₂` is finitely generated, then we can choose `Q ∈ AH₀`, and if
`K(Gᵢ) = {1}`, then for any finite subset `Fᵢ ⊂ Gᵢ`, we can choose `αᵢ` to be injective on
`Fᵢ`."* -/
def PrintedHullCorollary74 : Prop :=
  ∀ {G₁ G₂ : Type} [Group G₁] [Group G₂], IsAcylindricallyHyperbolic G₁ →
    IsAcylindricallyHyperbolic G₂ → Group.FG G₁ → Countable G₂ →
      ∀ (F₁ : Set G₁) (F₂ : Set G₂), F₁.Finite → F₂.Finite →
        ∃ (Q : Type) (_ : Group Q) (α₁ : G₁ →* Q) (α₂ : G₂ →* Q),
          ¬ GGT.IsVirtuallyCyclic Q ∧ Function.Surjective α₁ ∧ Function.Surjective α₂ ∧
            (Group.FG G₂ → IsAH0 Q) ∧
            (HasTrivialFiniteRadical G₁ → Set.InjOn α₁ F₁) ∧
            (HasTrivialFiniteRadical G₂ → Set.InjOn α₂ F₂)

/-- Hull's Corollary 7.4 from Theorem 7.1. -/
theorem printedHullCorollary74_of_tower (htower : HullSC.HullTowerStatementGeneral.{0}) :
    PrintedHullCorollary74 := by
  intro G₁ G₂ _ _ hah₁ hah₂ hfg₁ hcount₂ F₁ F₂ hF₁ hF₂
  -- `Gᵢ / K(Gᵢ) ∈ AH₀`
  obtain ⟨hah₁', hK₁⟩ := HullLemma510.printedHullLemma510 hah₁
  obtain ⟨hah₂', hK₂⟩ := HullLemma510.printedHullLemma510 hah₂
  haveI := hah₁'
  haveI := hah₂'
  obtain ⟨A⟩ := exists_hullGeneratingSet (G₁ ⧸ finiteRadical G₁)
  obtain ⟨B⟩ := exists_hullGeneratingSet (G₂ ⧸ finiteRadical G₂)
  have hπ₁ : Function.Surjective (QuotientGroup.mk' (finiteRadical G₁)) :=
    QuotientGroup.mk'_surjective _
  have hπ₂ : Function.Surjective (QuotientGroup.mk' (finiteRadical G₂)) :=
    QuotientGroup.mk'_surjective _
  obtain ⟨Q, instQ, β₁, β₂, hnvc, hβ₁, hβ₂, hAH0, hinj₁, hinj₂⟩ :=
    exists_commonQuotient_of_hullGeneratingSet htower A B hK₁ hK₂
      (Group.fg_of_surjective (hG := hfg₁) hπ₁) hπ₂.countable
      (hF₁.image (QuotientGroup.mk' (finiteRadical G₁)))
      (hF₂.image (QuotientGroup.mk' (finiteRadical G₂)))
  refine ⟨Q, instQ, β₁.comp (QuotientGroup.mk' (finiteRadical G₁)),
    β₂.comp (QuotientGroup.mk' (finiteRadical G₂)), hnvc, hβ₁.comp hπ₁, hβ₂.comp hπ₂,
    fun h => hAH0 (Group.fg_of_surjective (hG := h) hπ₂), fun h => ?_, fun h => ?_⟩
  · intro x hx y hy hxy
    have hq := hinj₁ (Set.mem_image_of_mem _ hx) (Set.mem_image_of_mem _ hy) hxy
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      hasTrivialFiniteRadical_iff_finiteRadical_eq_bot.mp h, Subgroup.mem_bot,
      inv_mul_eq_one] at hq
    exact hq
  · intro x hx y hy hxy
    have hq := hinj₂ (Set.mem_image_of_mem _ hx) (Set.mem_image_of_mem _ hy) hxy
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      hasTrivialFiniteRadical_iff_finiteRadical_eq_bot.mp h, Subgroup.mem_bot,
      inv_mul_eq_one] at hq
    exact hq

#audit_axioms printedHullCorollary74_of_tower

/-- Hull's Corollary 7.4 from the two least-area wall statements behind Theorem 7.1. -/
theorem printedHullCorollary74_of_leastAreaLeaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0}) :
    PrintedHullCorollary74 :=
  printedHullCorollary74_of_tower
    (HullSC.hullTowerStatementGeneral_of_leastAreaLeaves hgreendlinger hbridge)

#audit_axioms printedHullCorollary74_of_leastAreaLeaves

/-- Hull's Corollary 7.4 from the least-area Greendlinger wall alone: the embedded bridge is
`HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed`. -/
theorem printedHullCorollary74_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    PrintedHullCorollary74 :=
  printedHullCorollary74_of_leastAreaLeaves hgreendlinger
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed

#audit_axioms printedHullCorollary74_of_greendlinger

end HullCorollary74
end NonMF
end Manuscript
end GroupApproximation
