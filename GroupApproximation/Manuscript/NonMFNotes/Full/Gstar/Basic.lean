import GroupApproximation.Sofic.VerticalAscendingHNN
import GroupApproximation.Monsters.AffineSL3Doubling
import GroupApproximation.Meta.AxiomGuard

/-!
# The group `G_*`: the ascending HNN extension of `Γ_* = ℤ³ ⋊ SL₃(ℤ)`

Manuscript `non_mf_group_notes.tex`, subsection "The heightwise abelian quotient"
(tex lines 1943--1960), and the standing notation of `cor:notes-a5-relation`
(tex lines 2052--2073):

> Let `Γ_* = ℤ³ ⋊ SL₃(ℤ)` and `α(v,A) = (2v,A)`, and let `G_*` be the ascending HNN
> extension of `Γ_*` along `α`, `X = G_*/Γ_*`.

This file is the stable definition file of lane NN05; other lanes (NN04,
`VisibleQuotient`) import it.  Main declarations:

* `GammaStar` — `Γ_* = ℤ³ ⋊ SL₃(ℤ)` (the repository's `AffineSL3Doubling.Gamma`);
* `alphaStar`, `alphaStar_injective` — `α(v,A) = (2v,A)`;
* `doublingIso` — `α` read as the isomorphism `Γ_* ≃* α(Γ_*)`;
* `Gstar` — the literal Mathlib ascending HNN extension `HNNExtension Γ_* ⊤ α(Γ_*) α`;
* `ofGamma`, `ofGamma_injective` — the base embedding `Γ_* ↪ G_*`;
* `stableLetter` — the stable letter `t`;
* `stableLetter_conj`, `stableLetter_mul_ofGamma` — the relation `t γ t⁻¹ = α(γ)`;
* `gstarLift`, `gstarLift_ofGamma`, `gstarLift_stableLetter`, `gstar_hom_ext` — the universal
  property;
* `GstarCosets` — the coset space `X = G_*/Γ_*`, with its `G_*`-action, and `baseCoset`.
-/

namespace GroupApproximation.Full.NN05

noncomputable section

/-- `Γ_* = ℤ³ ⋊ SL₃(ℤ)` (tex line 1944). -/
abbrev GammaStar : Type := AffineSL3Doubling.Gamma

/-- The doubling endomorphism `α(v,A) = (2v,A)` of `Γ_*` (tex line 1944). -/
abbrev alphaStar : GammaStar →* GammaStar := AffineSL3Doubling.alpha

theorem alphaStar_injective : Function.Injective alphaStar :=
  AffineSL3Doubling.alpha_injective

/-- `α`, read as an isomorphism from all of `Γ_*` onto its image `α(Γ_*)`. -/
abbrev doublingIso : (⊤ : Subgroup GammaStar) ≃* alphaStar.range :=
  VerticalAscendingHNN.ascendingIso alphaStar alphaStar_injective

/-- **`G_*`**, the ascending HNN extension of `Γ_*` along `α` (tex lines 1944--1945),
as the literal Mathlib HNN extension with associated subgroups `Γ_*` and `α(Γ_*)`. -/
abbrev Gstar : Type := HNNExtension GammaStar ⊤ alphaStar.range doublingIso

/-- The base embedding `Γ_* → G_*`. -/
abbrev ofGamma : GammaStar →* Gstar := HNNExtension.of

/-- The stable letter `t ∈ G_*`. -/
abbrev stableLetter : Gstar := HNNExtension.t

/-- The base group `Γ_*` embeds in `G_*` (Britton's lemma, via Mathlib). -/
theorem ofGamma_injective : Function.Injective ofGamma :=
  HNNExtension.of_injective doublingIso

/-- The defining relation of the ascending HNN extension: `t γ t⁻¹ = α(γ)`. -/
theorem stableLetter_conj (g : GammaStar) :
    stableLetter * ofGamma g * stableLetter⁻¹ = ofGamma (alphaStar g) :=
  (HNNExtension.equiv_eq_conj (φ := doublingIso) ⟨g, Subgroup.mem_top g⟩).symm

/-- The defining relation in the form `t γ = α(γ) t`. -/
theorem stableLetter_mul_ofGamma (g : GammaStar) :
    stableLetter * ofGamma g = ofGamma (alphaStar g) * stableLetter :=
  HNNExtension.t_mul_of (φ := doublingIso) ⟨g, Subgroup.mem_top g⟩

section Lift

variable {H : Type*} [Group H]

/-- The universal property of `G_*`: a homomorphism on `Γ_*` together with an element
`x` satisfying `x f(γ) = f(α γ) x` extends uniquely to `G_*`. -/
abbrev gstarLift (f : GammaStar →* H) (x : H)
    (hx : ∀ g : GammaStar, x * f g = f (alphaStar g) * x) : Gstar →* H :=
  HNNExtension.lift f x (fun a => hx a)

theorem gstarLift_ofGamma (f : GammaStar →* H) (x : H)
    (hx : ∀ g : GammaStar, x * f g = f (alphaStar g) * x) (g : GammaStar) :
    gstarLift f x hx (ofGamma g) = f g :=
  HNNExtension.lift_of f x _ g

theorem gstarLift_stableLetter (f : GammaStar →* H) (x : H)
    (hx : ∀ g : GammaStar, x * f g = f (alphaStar g) * x) :
    gstarLift f x hx stableLetter = x :=
  HNNExtension.lift_t f x _

/-- Homomorphisms out of `G_*` are determined by their values on `Γ_*` and on `t`. -/
theorem gstar_hom_ext {f g : Gstar →* H} (hof : f.comp ofGamma = g.comp ofGamma)
    (ht : f stableLetter = g stableLetter) : f = g :=
  HNNExtension.hom_ext hof ht

end Lift

/-- The coset space `X = G_*/Γ_*` (tex line 1945), with the left translation action. -/
abbrev GstarCosets : Type := Gstar ⧸ ofGamma.range

/-- The base point `Γ_* ∈ X`. -/
abbrev baseCoset : GstarCosets := (QuotientGroup.mk 1 : Gstar ⧸ ofGamma.range)

example : MulAction Gstar GstarCosets := inferInstance

end

#audit_axioms ofGamma_injective
#audit_axioms stableLetter_conj
#audit_axioms stableLetter_mul_ofGamma
#audit_axioms gstarLift_ofGamma
#audit_axioms gstarLift_stableLetter
#audit_axioms gstar_hom_ext

end GroupApproximation.Full.NN05
