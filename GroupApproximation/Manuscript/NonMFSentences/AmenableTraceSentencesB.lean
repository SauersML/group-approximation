import GroupApproximation.Sofic.CliffordWitnessDirectDefect
import GroupApproximation.Sofic.CliffordLampNormalForm
import GroupApproximation.Manuscript.OneSidedMFRadical.AffineCliffordTrace
import GroupApproximation.Meta.AxiomGuard

/-!
# Printed sentences of `prop:clifford-self-embedding` and the concrete instance

`non_mf_groups_exist.tex` lines 1387-1550 cover the construction of the affine Clifford witness
`W`, Proposition `prop:clifford-self-embedding` and its proof, Proposition `prop:clifford-locally-rf`
and its proof, the concrete instance `Γ̄ = ℤ³ ⋊ SL₃(ℤ)`, and the proof of Theorem
`thm:amenable-trace`.  Most of these printed sentences already have carriers:
`Sofic/CliffordConstructionSentences.lean` covers the `Cl(X)` construction and the first half of
`prop:clifford-self-embedding`'s proof; `Sofic/CliffordWitnessSoficSentences.lean` covers
`prop:clifford-locally-rf`'s proof and the proof of `thm:amenable-trace`; the two propositions'
own statements, and several individual proof clauses, already have exact named carriers in
`Sofic/CliffordWitnessDirectDefect.lean`, `Manuscript/OneSidedMFRadical/AffineCliffordTrace.lean`,
and elsewhere (see the sentence-census rows for this module).

This module supplies `manuscriptSentence_<slug>` carriers for the printed sentences in that range
that had no carrier yet: the middle of `prop:clifford-self-embedding`'s proof (the root lamp's
centralizing/fixing clause, the distinct-lamps-are-involutions-with-nontrivial-commutator clause,
the `d = [x,a] = xy`, `d² = [x,y] = ε` factorization, and the "`⟨ε⟩` is central, normal, finite,
hence has `(T)`" clause), the "killing `ε`" central-extension clause for `Cl(X)`, and the
concrete instance's "`α` is injective, has index eight, and `a` escapes its range" clause at the
literal `gammaBar`/`conjD` model used by the rest of the development (as opposed to the
independent matrix model `Monsters/AffineSL3Doubling.lean` feeds into the index computation).
Every proof below is a direct projection from already-landed declarations: no new mathematics.
-/

namespace GroupApproximation
namespace AmenableTraceSentencesB

open MarkedCompression CliffordLamp CliffordWitnessDirectDefect
open scoped commutatorElement

noncomputable section

/-! ## `prop:clifford-self-embedding`'s proof, first sentence -/

/-- **Printed sentence** (`non_mf_groups_exist.tex:1443-1445`).

> Identify `Γ` with its level-zero copy in `V ≤ W`, and let `c` be the lamp at the root coset
> `Γ ∈ X`; it centralizes `Γ`, which fixes that coset.

`c` is `cAmbient α hα`, the lamp at the root coset (`rootCoset α hα`); it centralizes the copy of
`Γ` (`comm_c`), and that copy fixes the root coset (`iotaVertical_smul_rootCoset`). -/
theorem manuscriptSentence_rootLampCentralizesFixesCoset
    {Γ : Type} [Group Γ] (α : Γ →* Γ) (hα : Function.Injective α) :
    (∀ γ : Γ, Commute (cAmbient α hα) (iotaAmbient α hα γ)) ∧
      (∀ γ : Γ, iotaVertical α hα γ • rootCoset α hα = rootCoset α hα) :=
  ⟨comm_c α hα, iotaVertical_smul_rootCoset α hα⟩

/-! ## `prop:clifford-self-embedding`'s proof, the two central algebraic sentences -/

/-- **Printed sentence** (`non_mf_groups_exist.tex:1448-1449`).

> so `x = tct^{-1}` and `y = axa^{-1}` are distinct lamps, involutions with `[x,y] = ε ≠ 1`.

`x` is `compressionRoot α hα`; `y` is its `ι(a)`-conjugate.  Both are involutions
(`compressionRoot_sq`, and `conj_sq_eq_one` applied to it); their commutator is the central sign
(`commutator_conjugate_eq_commutator_sq_of_sq_eq_one` composed with `sign_eq_pointDefect_sq`,
which is the same identity the manuscript's next sentence names `d²`); the sign is nontrivial
(`signAmbient_ne_one`); and `x ≠ y` because `x = y` would force `⁅x,y⁆ = ⁅x,x⁆ = 1 ≠ ε`. -/
theorem manuscriptSentence_distinctInvolutionsCommutatorSign
    {Γ : Type} [Group Γ] (α : Γ →* Γ) (hα : Function.Injective α)
    {a : Γ} (ha : a ∉ Set.range α) :
    compressionRoot α hα ≠
        iotaAmbient α hα a * compressionRoot α hα * (iotaAmbient α hα a)⁻¹ ∧
      compressionRoot α hα ^ 2 = 1 ∧
      (iotaAmbient α hα a * compressionRoot α hα * (iotaAmbient α hα a)⁻¹) ^ 2 = 1 ∧
      ⁅compressionRoot α hα,
          iotaAmbient α hα a * compressionRoot α hα * (iotaAmbient α hα a)⁻¹⁆ =
        signAmbient α hα ∧
      signAmbient α hα ≠ 1 := by
  have hxsq : compressionRoot α hα ^ 2 = 1 := compressionRoot_sq α hα
  have hysq : (iotaAmbient α hα a * compressionRoot α hα * (iotaAmbient α hα a)⁻¹) ^ 2 = 1 :=
    conj_sq_eq_one (compressionRoot α hα) (iotaAmbient α hα a) hxsq
  have hcomm : ⁅compressionRoot α hα,
      iotaAmbient α hα a * compressionRoot α hα * (iotaAmbient α hα a)⁻¹⁆ =
        signAmbient α hα := by
    rw [commutator_conjugate_eq_commutator_sq_of_sq_eq_one (compressionRoot α hα)
      (iotaAmbient α hα a) hxsq]
    exact (sign_eq_pointDefect_sq α hα ha).symm
  have hsignne : signAmbient α hα ≠ 1 := signAmbient_ne_one α hα
  refine ⟨fun heq ↦ ?_, hxsq, hysq, hcomm, hsignne⟩
  apply hsignne
  have hxy :
      (⁅compressionRoot α hα,
          iotaAmbient α hα a * compressionRoot α hα * (iotaAmbient α hα a)⁻¹⁆ :
            Ambient α hα) =
        ⁅iotaAmbient α hα a * compressionRoot α hα * (iotaAmbient α hα a)⁻¹,
            iotaAmbient α hα a * compressionRoot α hα * (iotaAmbient α hα a)⁻¹⁆ :=
    congrArg (fun z ↦ ⁅z, iotaAmbient α hα a * compressionRoot α hα *
      (iotaAmbient α hα a)⁻¹⁆) heq
  rw [← hcomm, hxy, commutatorElement_def]
  group

/-- **Printed sentence** (`non_mf_groups_exist.tex:1450`).

> Then `d = [x,a] = xy` and `d² = xyxy = [x,y] = ε`,

`d` is `pointDefect α hα a := ⁅compressionRoot α hα, ι(a)⁆`.  The factorization `d = xy` is
`commutator_eq_mul_conj`; the reading of `d²` as `[x,y]` is
`commutator_conjugate_eq_commutator_sq_of_sq_eq_one`; and `d² = ε` is `sign_eq_pointDefect_sq`. -/
theorem manuscriptSentence_defectFactorization
    {Γ : Type} [Group Γ] (α : Γ →* Γ) (hα : Function.Injective α)
    {a : Γ} (ha : a ∉ Set.range α) :
    pointDefect α hα a =
        compressionRoot α hα *
          (iotaAmbient α hα a * compressionRoot α hα * (iotaAmbient α hα a)⁻¹) ∧
      pointDefect α hα a ^ 2 =
        ⁅compressionRoot α hα,
            iotaAmbient α hα a * compressionRoot α hα * (iotaAmbient α hα a)⁻¹⁆ ∧
      pointDefect α hα a ^ 2 = signAmbient α hα :=
  ⟨commutator_eq_mul_conj (compressionRoot α hα) (iotaAmbient α hα a) (compressionRoot_sq α hα),
    (commutator_conjugate_eq_commutator_sq_of_sq_eq_one (compressionRoot α hα)
      (iotaAmbient α hα a) (compressionRoot_sq α hα)).symm,
    (sign_eq_pointDefect_sq α hα ha).symm⟩

/-! ## `prop:clifford-self-embedding`'s proof, the sign subgroup -/

/-- **Printed sentence** (`non_mf_groups_exist.tex:1453-1454`).

> The subgroup `⟨ε⟩` is central, so normal, and it is finite, so it has property `(T)`.

`⟨ε⟩` is `signSubgroup α hα`; centrality of its generator is `signAmbient_central`, normality is
the instance `signSubgroup_normal`, finiteness is the instance `signSubgroup_finite`, and every
finite group has property `(T)` (`hasKazhdanPropertyT_of_finite`). -/
theorem manuscriptSentence_signSubgroupCentralNormalFiniteHasT
    {Γ : Type} [Group Γ] (α : Γ →* Γ) (hα : Function.Injective α) :
    (∀ g : Ambient α hα, Commute (signAmbient α hα) g) ∧
      (signSubgroup α hα).Normal ∧
      Finite (signSubgroup α hα) ∧
      HasKazhdanPropertyT.{0, 0} (signSubgroup α hα) :=
  ⟨signAmbient_central α hα, signSubgroup_normal α hα, signSubgroup_finite α hα,
    hasKazhdanPropertyT_of_finite (signSubgroup α hα)⟩

/-! ## The `Cl(X)` construction, the "killing `ε`" clause -/

/-- **Printed sentence** (`non_mf_groups_exist.tex:1421-1424`, first half).

> Killing `ε` leaves `F₂^{(X)} ≅ ⊕_X C₂`, so `Cl(X)` is a central extension of `⊕_X C₂` by `C₂`.

The "killing `ε`" map is `config ∘ toModel X : Cl(X) → (X →₀ ZMod 2)`, the second coordinate of
the printed isomorphism `toModel X` (`Sofic/CliffordLampGroup.lean`, proved bijective in
`Sofic/CliffordLampNormalForm.lean`).  It is surjective onto the printed `F₂^{(X)} = X →₀ ZMod 2`
(every finitely supported function is `(toModel X)`'s second coordinate at some group element,
since `toModel X` is onto `SignedModel X`), its fibre over `0` is exactly `{1, ε}` (case-splitting
on the two elements of `ZMod 2` and using injectivity of `toModel X`), and `ε` is central
(`sign_commute`).  This is the printed central extension `1 → ⟨ε⟩ → Cl(X) → F₂^{(X)} → 1`.  (The
second half of the printed sentence, that `W` itself is a central extension of the permutational
wreath product `C₂ ≀_X V` by `⟨ε⟩`, is not formalized here: it needs the wreath-product structure
on `(X →₀ ZMod 2) ⋊ V`, which is not otherwise part of the repository's route to the manuscript's
conclusions and would be new infrastructure disproportionate to this one expository remark.) -/
theorem manuscriptSentence_cliffordLampKillSignCentralExtension
    {X : Type} [LinearOrder X] :
    Function.Surjective (fun w : CliffordLamp X ↦ (toModel X w).config) ∧
      (∀ w : CliffordLamp X, (toModel X w).config = 0 ↔ w = 1 ∨ w = sign X) ∧
      (∀ g : CliffordLamp X, Commute (sign X) g) := by
  obtain ⟨hbij, -, -⟩ := CliffordLampNormalForm.toModel_bijective_printed (X := X)
  refine ⟨fun f ↦ ?_, fun w ↦ ⟨fun hcfg ↦ ?_, ?_⟩, sign_commute X⟩
  · obtain ⟨w, hw⟩ := hbij.surjective (⟨0, f⟩ : SignedModel X)
    exact ⟨w, by simp [hw]⟩
  · have hZ2 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    rcases hZ2 (toModel X w).signPart with h0 | h1
    · refine Or.inl (hbij.injective ?_)
      rw [map_one]
      apply SignedModel.ext <;> simp [h0, hcfg]
    · refine Or.inr (hbij.injective ?_)
      rw [toModel_sign]
      apply SignedModel.ext <;> simp [h1, hcfg, modelSign]
  · rintro (rfl | rfl)
    · simp [map_one, one_def]
    · simp [toModel_sign, modelSign]

/-! ## The concrete instance, the doubling data -/

/-- **Printed sentence** (`non_mf_groups_exist.tex:1538-1541`).

> This is injective, and its image consists of the affine matrices whose translation coordinates
> are all even, so `[Γ̄ : α(Γ̄)] = 8`.  Translation `a` by the first standard basis vector lies
> outside `α(Γ̄)`.

At the literal model `gammaBar`/`conjD` (`Monsters/ExplicitLinearModel.lean`,
`Sofic/LiteralNonMFLinearWitness.lean`) that the rest of the development uses for `Γ̄` and `α`:
injectivity is `ExplicitLinearModel.conjD_injective`; the index-eight and escaping-translation
facts are exactly `AmenableTraceTheorem.manuscriptAffineCliffordHypotheses`.  (The even-translation
image description is proved at the *independent* matrix model `Monsters/AffineSL3Doubling.lean`,
which feeds the same index-eight computation via `Sofic/LiteralAffineRangeIndexEight.lean`:
`AffineSL3Doubling.mem_range_alpha_iff`.) -/
theorem manuscriptSentence_concreteInstanceDoubling :
    Function.Injective ExplicitLinearModel.conjD ∧
      AmenableTraceTheorem.PrintedAffineCliffordHypotheses :=
  ⟨ExplicitLinearModel.conjD_injective, AmenableTraceTheorem.manuscriptAffineCliffordHypotheses⟩

end

end AmenableTraceSentencesB
end GroupApproximation

open GroupApproximation
open GroupApproximation.AmenableTraceSentencesB

#audit_axioms manuscriptSentence_rootLampCentralizesFixesCoset
#audit_axioms manuscriptSentence_distinctInvolutionsCommutatorSign
#audit_axioms manuscriptSentence_defectFactorization
#audit_axioms manuscriptSentence_signSubgroupCentralNormalFiniteHasT
#audit_axioms manuscriptSentence_cliffordLampKillSignCentralExtension
#audit_axioms manuscriptSentence_concreteInstanceDoubling
