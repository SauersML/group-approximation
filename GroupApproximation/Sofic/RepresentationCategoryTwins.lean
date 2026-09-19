import GroupApproximation.Sofic.LinearResidual

/-!
# The twins have the same representation *category*, not just the same
# representations

Proposition 48.8.  `Sofic/ProfiniteTwins.precomp_bijective` already says that
precomposition with an invisible quotient is a bijection on *objects*: every
finite-target representation of the group comes from the quotient, uniquely.
That is a statement about Hom-sets and it leaves the morphisms untouched.

Proposition 48.8 upgrades it to an equivalence of categories: the intertwiner
spaces agree as well.  This is the difference between "the two groups have the
same representations" and "they have the same representation theory", and it is
what makes the twin phenomenon sharp -- the pair cannot be told apart by any
construction built out of finite-dimensional representations and maps between
them, only by asking whether one of those representations happens to be
faithful.

## The two halves

**Full faithfulness** is `intertwines_iff`, and it needs nothing but
surjectivity of the quotient map.  A linear map intertwines the inflated
representations exactly when it intertwines the original ones, because
surjectivity means the two families of equations are indexed by the same set:
every `p` is `q g` for some `g`.  No hypothesis on the kernel is used here.

**Essential surjectivity on objects** is `precompLinear_surjective`, and this is
where the kernel hypothesis enters: if `ker q` lies in the linear residual then
every finite-dimensional representation of `G` kills it, hence factors through
`q`.  Injectivity (`precompLinear_injective`) is again just surjectivity of `q`.

Together they give `precompLinear_bijective` and the packaged statement
`representation_category_equiv`.

## Scope

Stated for an arbitrary field and arbitrary dimensions, and for the abstract
hypothesis `q.ker ≤ linearResidual G` rather than for any particular
construction -- so it applies to every twin pair in the development at once, in
particular the perfect-lamp pair where the invisible kernel is the whole lamp
subgroup.

Representations are `MonoidHom`s into the multiplicative monoid of square
matrices, matching `linearResidual`; nothing here needs invertibility, and the
intertwining statement is about rectangular matrices between the two dimensions.
-/

namespace GroupApproximation

namespace RepresentationCategoryTwins

universe u

variable {G : Type u} [Group G] {P : Type u} [Group P]

/-! ## Full faithfulness: the intertwiner spaces agree -/

/-- **The morphism half of Proposition 48.8.**  A linear map intertwines two
inflated representations exactly when it intertwines the two originals.

Only surjectivity of `q` is used: it makes the two families of equations range
over the same index set.  In particular this half holds for *every* surjection,
invisible kernel or not. -/
theorem intertwines_iff (q : G →* P) (hq : Function.Surjective q)
    {F : Type} [Field F] {d₁ d₂ : ℕ}
    (ρ₁ : P →* Matrix (Fin d₁) (Fin d₁) F)
    (ρ₂ : P →* Matrix (Fin d₂) (Fin d₂) F)
    (T : Matrix (Fin d₂) (Fin d₁) F) :
    (∀ g : G, T * ρ₁ (q g) = ρ₂ (q g) * T)
      ↔ (∀ p : P, T * ρ₁ p = ρ₂ p * T) := by
  constructor
  · intro h p
    obtain ⟨g, rfl⟩ := hq p
    exact h g
  · intro h g
    exact h (q g)

/-! ## Objects: inflation is a bijection on representations -/

/-- Inflation of a representation along `q`. -/
def precompLinear (q : G →* P) (F : Type) [Field F] (d : ℕ) :
    (P →* Matrix (Fin d) (Fin d) F) → (G →* Matrix (Fin d) (Fin d) F) :=
  fun ρ => ρ.comp q

@[simp] theorem precompLinear_apply (q : G →* P) (F : Type) [Field F] (d : ℕ)
    (ρ : P →* Matrix (Fin d) (Fin d) F) (g : G) :
    precompLinear q F d ρ g = ρ (q g) := rfl

theorem precompLinear_injective (q : G →* P) (hq : Function.Surjective q)
    (F : Type) [Field F] (d : ℕ) :
    Function.Injective (precompLinear q F d) := by
  intro ρ₁ ρ₂ h
  refine MonoidHom.ext fun p => ?_
  obtain ⟨g, rfl⟩ := hq p
  exact congrArg (fun f : G →* Matrix (Fin d) (Fin d) F => f g) h

/-- **The object half.**  If the kernel is invisible to finite-dimensional
linear representations then every representation of `G` is inflated from `P`. -/
theorem precompLinear_surjective (q : G →* P) (hq : Function.Surjective q)
    (hker : q.ker ≤ linearResidual G) (F : Type) [Field F] (d : ℕ) :
    Function.Surjective (precompLinear q F d) := by
  intro σ
  have hkerle : q.ker ≤ (σ : G →* Matrix (Fin d) (Fin d) F).ker := by
    intro x hx
    exact hker hx F inferInstance d σ
  refine ⟨(QuotientGroup.lift q.ker σ hkerle).comp
      (QuotientGroup.quotientKerEquivOfSurjective q hq).symm.toMonoidHom, ?_⟩
  refine MonoidHom.ext fun g => ?_
  show QuotientGroup.lift q.ker σ hkerle
      ((QuotientGroup.quotientKerEquivOfSurjective q hq).symm (q g)) = σ g
  have hsymm : (QuotientGroup.quotientKerEquivOfSurjective q hq).symm (q g)
      = QuotientGroup.mk g := by
    apply (QuotientGroup.quotientKerEquivOfSurjective q hq).injective
    rw [MulEquiv.apply_symm_apply]
    rfl
  rw [hsymm]
  rfl

theorem precompLinear_bijective (q : G →* P) (hq : Function.Surjective q)
    (hker : q.ker ≤ linearResidual G) (F : Type) [Field F] (d : ℕ) :
    Function.Bijective (precompLinear q F d) :=
  ⟨precompLinear_injective q hq F d, precompLinear_surjective q hq hker F d⟩

/-! ## The packaged statement -/

/-- **Proposition 48.8.**  Precomposition with an invisible quotient is an
equivalence of finite-dimensional representation categories over every field:
a bijection on objects, and an equality of intertwiner spaces.

The pair is therefore indistinguishable by anything built from
finite-dimensional representations and the maps between them.  What separates
them is not which representations exist but whether one of them is faithful --
which is exactly the MF question, and is invisible to this data. -/
theorem representation_category_equiv (q : G →* P) (hq : Function.Surjective q)
    (hker : q.ker ≤ linearResidual G) (F : Type) [Field F] :
    (∀ d : ℕ, Function.Bijective (precompLinear q F d)) ∧
      (∀ (d₁ d₂ : ℕ) (ρ₁ : P →* Matrix (Fin d₁) (Fin d₁) F)
        (ρ₂ : P →* Matrix (Fin d₂) (Fin d₂) F)
        (T : Matrix (Fin d₂) (Fin d₁) F),
        (∀ g : G, T * precompLinear q F d₁ ρ₁ g
            = precompLinear q F d₂ ρ₂ g * T)
          ↔ (∀ p : P, T * ρ₁ p = ρ₂ p * T)) :=
  ⟨fun d => precompLinear_bijective q hq hker F d,
    fun _ _ ρ₁ ρ₂ T => intertwines_iff q hq ρ₁ ρ₂ T⟩

end RepresentationCategoryTwins

end GroupApproximation
