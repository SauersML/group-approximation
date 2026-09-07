import GroupApproximation.Sofic.MarkedCompressionGroup
import GroupApproximation.Sofic.CliffordLampPermanence
import GroupApproximation.Sofic.CliffordLampNormalForm
import GroupApproximation.Sofic.CliffordLampOrderFormula
import GroupApproximation.Sofic.SoficTelescope
import GroupApproximation.Monsters.AffineSL3Doubling
import GroupApproximation.Meta.AxiomGuard

/-!
# The concrete Clifford lamp construction, printed sentences

Three pockets of `non_mf_groups_exist.tex` describe the *concrete* Clifford lamp
construction (generators and relations for `Cl(X)`, the `𝔽₂`-vector-space cocycle used to show
the central sign is nontrivial, the order computation, the automorphism action) while the
repository's route to the same conclusions goes through the abstract
`MarkedCompressionGroup`/`Ambient` model.  This module gives `manuscriptSentence_<slug>` wrappers,
following `Sofic/CliffordWitnessSoficSentences.lean`'s pattern, for every printed sentence in
those pockets that is already carried --- almost all of them, since `Sofic/CliffordLampGroup.lean`
already realizes the printed construction essentially verbatim: `sign`/`lamp` are the printed
generators `ε`/`c_x`; `IsRelator` is the printed relation set; `crossing` is the printed cocycle
`B`; `SignedModel` is the printed `𝔽₂ × E`; `toModel` is the printed homomorphism; and `permHom`
is the printed permutation-automorphism action.

Every printed sentence in those pockets now has a carrier.  Countability and local finiteness of
`Cl(X)` are proved by an unrelated route (`Sofic/CentralInvolutionFinite.lean`'s generic
central-involution argument) from the exact order `2^{|Y|+1}` (`Sofic/CliffordLampOrderFormula.lean`,
built from `Sofic/CliffordLampNormalForm.lean`'s normal-form theorem), so those three clauses are
combined into one lemma below rather than derived from each other.
-/

namespace GroupApproximation
namespace CliffordConstructionSentences

open MarkedCompression CliffordLamp MappingTelescope SemidirectProduct
open scoped commutatorElement

noncomputable section

/-! ## `prop:locally-rf-by-z-trace`'s proof preamble (the construction of `W`) -/

/-- **Printed sentence.**

> where `tgt^{-1} = α(g)` on the level-zero copy of `Γ`, so that `V` is the ascending HNN
> extension of `Γ` along `α` and `T_α = ⋃_{n≥0} t^{-n} Γ t^n`.

The conjugation formula is `vertical_compress`; the exhaustion of `T_α` by level copies of `Γ` is
`exists_level_repr`. -/
theorem manuscriptSentence_hnnExtension {Γ : Type} [Group Γ]
    (α : Γ →* Γ) (hα : Function.Injective α) :
    (∀ g : Γ, tVertical α hα * iotaVertical α hα g * (tVertical α hα)⁻¹ =
        iotaVertical α hα (α g)) ∧
      (∀ x : Telescope α hα, ∃ (n : ℕ) (g : Γ), level α hα n g = x) :=
  ⟨vertical_compress α hα, exists_level_repr α hα⟩

/-- **Printed sentence** (the generators-and-relations display).

> The Clifford lamp group `Cl(X)` is the group with generators `ε` and `c_x`, `x ∈ X`, and
> relations `ε² = c_x² = 1`, `[ε,c_x] = 1`, `[c_x,c_y] = ε` (`x ≠ y`).

`CliffordLamp X := PresentedGroup (relators X)` is presented by exactly these four relator
families (`IsRelator`); the four displayed relations are `sign_sq`, `lamp_sq`,
`sign_commute_lamp`, `commutator_lamp_lamp`. -/
theorem manuscriptSentence_cliffordLampPresentation {X : Type} :
    sign X ^ 2 = 1 ∧ (∀ x : X, lamp X x ^ 2 = 1) ∧
      (∀ x : X, Commute (sign X) (lamp X x)) ∧
      (∀ x y : X, x ≠ y → ⁅lamp X x, lamp X y⁆ = sign X) :=
  ⟨sign_sq X, lamp_sq X, sign_commute_lamp X, fun _ _ h ↦ commutator_lamp_lamp X h⟩

/-- **Printed sentences** (the `𝔽₂ × E` cocycle model and its group-theoretic properties).

> Since `B` is bilinear, `(a,f)(b,g) = (a+b+B(f,g), f+g)` is a group law on `𝔽₂ × E`, in which
> `(1,0)` is a central involution, each `(0,δ_x)` is an involution, and for `x ≠ y` exactly one of
> `B(δ_x,δ_y)` and `B(δ_y,δ_x)` equals `1`, so the commutator of `(0,δ_x)` and `(0,δ_y)` is
> `(1,0)`.

`E = X →₀ ZMod 2` is the printed `𝔽₂`-vector space of finitely supported functions, `B` is
`crossing`, `𝔽₂ × E` is `SignedModel X`, and `(1,0)`/`(0,δ_x)` are `modelSign`/`modelLamp`.  Every
clause is proved: the displayed group law is `mul_def`, central-involution is
`modelSign_commute` + `modelSign_sq`, each lamp an involution is `modelLamp_sq`, the exactly-one-
crossing clause is `crossing_single_add_swap`, and the commutator clause is
`modelLamp_commutator`. -/
theorem manuscriptSentence_signedModelGroupLaw {X : Type} [LinearOrder X] :
    (∀ (a b : ZMod 2) (f g : X →₀ ZMod 2),
        (⟨a, f⟩ : SignedModel X) * ⟨b, g⟩ = ⟨a + b + crossing X f g, f + g⟩) ∧
      (∀ p : SignedModel X, Commute (modelSign X) p) ∧
      modelSign X ^ 2 = 1 ∧
      (∀ x : X, modelLamp X x ^ 2 = 1) ∧
      (∀ x y : X, x ≠ y →
        crossing X (Finsupp.single x 1) (Finsupp.single y 1) +
          crossing X (Finsupp.single y 1) (Finsupp.single x 1) = 1) ∧
      (∀ x y : X, x ≠ y → ⁅modelLamp X x, modelLamp X y⁆ = modelSign X) :=
  ⟨fun _ _ _ _ ↦ rfl, modelSign_commute X, modelSign_sq X, modelLamp_sq X,
    fun _ _ h ↦ crossing_single_add_swap X h, fun _ _ h ↦ modelLamp_commutator X h⟩

/-- **Printed sentence.**

> So `ε ↦ (1,0)`, `c_x ↦ (0,δ_x)` defines a homomorphism `Cl(X) → 𝔽₂ × E`.

`toModel`, built from `modelGenerator` killing every relator (`modelGenerator_kills`), is exactly
this homomorphism; `toModel_sign`/`toModel_lamp` are its values on the generators. -/
theorem manuscriptSentence_toModelHomomorphism {X : Type} [LinearOrder X] :
    toModel X (sign X) = modelSign X ∧ (∀ x : X, toModel X (lamp X x) = modelLamp X x) :=
  ⟨toModel_sign X, toModel_lamp X⟩

/-- **Printed sentence.**

> The relations let us write every element of `Cl(X)` as `ε^a c_{x_1}⋯c_{x_r}`, `a ∈ 𝔽₂`,
> `x_1 < ⋯ < x_r`, and this word maps to `(a,δ_{x_1}+⋯+δ_{x_r})`, so the expression is unique and
> the homomorphism is an isomorphism.

`CliffordLampNormalForm.toModel_bijective_printed`: `toModel X` is a bijection onto
`SignedModel X`, with explicit two-sided inverse `CliffordLampNormalForm.section'`, which sends
`⟨a,f⟩` to `ε^a` times the ascending word over `f`'s support --- exactly the printed word
`ε^a c_{x_1}⋯c_{x_r}`.  Existence of the word is `RightInverse section' (toModel X)`; uniqueness
of the expression is `Injective (toModel X)` (two words with the same image are equal); "the
homomorphism is an isomorphism" is the bijection itself. -/
theorem manuscriptSentence_cliffordLampNormalForm {X : Type} [LinearOrder X] :
    Function.Bijective (toModel X) ∧
      Function.LeftInverse CliffordLampNormalForm.section' (toModel X) ∧
      Function.RightInverse CliffordLampNormalForm.section' (toModel X) :=
  CliffordLampNormalForm.toModel_bijective_printed

/-- **Printed sentence.**

> In particular, for a finite subset `Y ⊆ X`, the subgroup generated by `ε` and the `c_y` with
> `y ∈ Y` has order `2^{|Y|+1}`, so `Cl(X)` is countable and locally finite.

The order formula is `CliffordLampOrderFormula.nat_card_closure`.  The countable/locally-finite
half is proved, but by an unrelated route: `Countable (CliffordLamp X)` is the presented group's
generic countable-generators instance, and `IsLocallyFiniteGroup (CliffordLamp X)` is
`isLocallyFiniteGroup_cliffordLamp`, via the generic central-involution finiteness theorem
(`Sofic/CentralInvolutionFinite.lean`), not via the printed order computation. -/
theorem manuscriptSentence_cliffordLampCountableLocallyFinite {X : Type} [LinearOrder X]
    [Countable X] :
    (∀ Y : Finset X,
        Nat.card (Subgroup.closure ({sign X} ∪ lamp X '' (↑Y : Set X))) = 2 ^ (Y.card + 1)) ∧
      Countable (CliffordLamp X) ∧ IsLocallyFiniteGroup (CliffordLamp X) :=
  ⟨CliffordLampOrderFormula.nat_card_closure, inferInstance, isLocallyFiniteGroup_cliffordLamp X⟩

/-- **Printed sentence.**

> The relations are invariant under permutations of `X`, so every permutation of `X` induces an
> automorphism of `Cl(X)` that permutes the `c_x` accordingly and fixes `ε`.

`permHom : Equiv.Perm X →* MulAut (CliffordLamp X)` is exactly this action;
`permHom_apply_sign`/`permHom_apply_lamp` are the "fixes `ε`"/"permutes the `c_x`" clauses. -/
theorem manuscriptSentence_permutationAutomorphism {X : Type} (e : Equiv.Perm X) :
    permHom X e (sign X) = sign X ∧ (∀ x : X, permHom X e (lamp X x) = lamp X (e x)) :=
  ⟨permHom_apply_sign X e, permHom_apply_lamp X e⟩

/-- **Printed sentence** (the naming "we put `W = Cl(X) ⋊ V`" is `MarkedCompression.Ambient`,
definitionally, and is not restated here).

> In this way `V` acts on `Cl(X)` through its action on `X`, and we put `W = Cl(X) ⋊ V`.

`lampAction` is exactly the composite "`V`'s action on `X` by left multiplication, then `X`'s
permutation action on `Cl(X)`"; `lampAction_apply_lamp`/`lampAction_apply_sign` record it on the
generators, and `Ambient α hα := CliffordLamp (Cosets α hα) ⋊[lampAction α hα] Vertical α hα` is
`W`. -/
theorem manuscriptSentence_verticalActsOnLamp {Γ : Type} [Group Γ]
    (α : Γ →* Γ) (hα : Function.Injective α) (v : Vertical α hα) (x : Cosets α hα) :
    lampAction α hα v (lamp (Cosets α hα) x) = lamp (Cosets α hα) (v • x) ∧
      lampAction α hα v (sign (Cosets α hα)) = sign (Cosets α hα) :=
  ⟨lampAction_apply_lamp α hα v x, lampAction_apply_sign α hα v⟩

/-! ## `prop:clifford-self-embedding`, printed proof -/

/-- **Printed sentence.**

> Then `tct^{-1}` is the lamp at `tΓ` and `a(tct^{-1})a^{-1}` is the lamp at `atΓ`.

`c` is `cAmbient α hα := inl (lamp (Cosets α hα) (rootCoset α hα))`, the lamp at the root coset
`Γ ∈ X` (`rootCoset`); `tΓ` is `tVertical α hα • rootCoset α hα`; both conjugation formulas are
`conj_inl_lamp`. -/
theorem manuscriptSentence_conjugatedLampsAtCosets {Γ : Type} [Group Γ]
    (α : Γ →* Γ) (hα : Function.Injective α) (a : Γ) :
    tAmbient α hα * cAmbient α hα * (tAmbient α hα)⁻¹ =
        inl (lamp (Cosets α hα) (tVertical α hα • rootCoset α hα)) ∧
      iotaAmbient α hα a *
          inl (lamp (Cosets α hα) (tVertical α hα • rootCoset α hα)) *
          (iotaAmbient α hα a)⁻¹ =
        inl (lamp (Cosets α hα)
          (iotaVertical α hα a • (tVertical α hα • rootCoset α hα))) := by
  refine ⟨conj_inl_lamp α hα _ _, ?_⟩
  show (inr (iotaVertical α hα a) : Ambient α hα) *
      inl (lamp (Cosets α hα) (tVertical α hα • rootCoset α hα)) *
      (inr (iotaVertical α hα a))⁻¹ = _
  rw [conj_inl_lamp]

/-- **Printed sentence.**

> These cosets are distinct, because `tΓ = atΓ` would mean `a ∈ tΓt^{-1} = α(Γ)`.

`moved_cosets_ne`, whose own proof runs exactly this contradiction (via `vertical_compress` and
`level_succ_mem_range_level_iff` identifying membership in a conjugated level-zero copy with
membership in `range α`). -/
theorem manuscriptSentence_movedCosetsDistinct {Γ : Type} [Group Γ]
    (α : Γ →* Γ) (hα : Function.Injective α) {a : Γ} (ha : a ∉ Set.range α) :
    tVertical α hα • rootCoset α hα ≠
      (iotaVertical α hα a * tVertical α hα) • rootCoset α hα :=
  moved_cosets_ne α hα ha

/-! ## `prop:clifford-locally-rf`, the concrete instance -/

/-- **Printed sentence.**

> so that `α(v,A) = (2v,A)`.

This is `Monsters/AffineSL3Doubling.lean`'s concrete affine model `Gamma = (Fin 3 → ℤ) ⋊
SL(3,ℤ)`, independent of the six-generator presentation `ExplicitLinearModel`/`gammaBar` uses
elsewhere but feeding the *same* index-eight computation via `LiteralAffineRangeIndexEight.lean`
(`latticeDouble := AffineSL3Doubling.doubleMul`).  `alpha_left`/`alpha_right` are exactly the two
coordinates of the printed formula. -/
theorem manuscriptSentence_alphaDoublesTranslation (g : AffineSL3Doubling.Gamma) :
    (AffineSL3Doubling.alpha g).left = AffineSL3Doubling.doubleMul g.left ∧
      (AffineSL3Doubling.alpha g).right = g.right :=
  ⟨AffineSL3Doubling.alpha_left g, AffineSL3Doubling.alpha_right g⟩

end

end CliffordConstructionSentences
end GroupApproximation

open GroupApproximation
open GroupApproximation.CliffordConstructionSentences

#audit_axioms manuscriptSentence_hnnExtension
#audit_axioms manuscriptSentence_cliffordLampPresentation
#audit_axioms manuscriptSentence_signedModelGroupLaw
#audit_axioms manuscriptSentence_toModelHomomorphism
#audit_axioms manuscriptSentence_cliffordLampNormalForm
#audit_axioms manuscriptSentence_cliffordLampCountableLocallyFinite
#audit_axioms manuscriptSentence_permutationAutomorphism
#audit_axioms manuscriptSentence_verticalActsOnLamp
#audit_axioms manuscriptSentence_conjugatedLampsAtCosets
#audit_axioms manuscriptSentence_movedCosetsDistinct
#audit_axioms manuscriptSentence_alphaDoublesTranslation
