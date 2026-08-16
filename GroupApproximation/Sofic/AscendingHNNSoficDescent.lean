import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.GroupAction.Quotient
import GroupApproximation.Sofic.SoficActionEmbedding

/-!
# Soficity of a coset action descends to the compressed subgroup

Proposition 1.1 of the 2026-08-16 audit.  The ascending-HNN coset action
`G ↷ G/Γ` is the object whose soficity is open in general (Section 38.4 of the
dossier: finite index and UAS/LERA are settled, the unrestricted case is not).
The audit observes that soficity of that action is not merely *sufficient* for
the wreath conclusion but carries information *downwards*: it forces soficity of
the compressed subgroup's own coset action `Γ ↷ Γ/α(Γ)`.

That is a genuine sharpening of the open problem, because it says a
counterexample cannot be manufactured at the ambient level while keeping the
base tame -- the base inherits the property.

## The mechanism

Only one thing is used, and it is finite-index-free and HNN-free.  Fix `Γ ≤ G`
and any `t ∈ G`.  The stabiliser of the site `tΓ` inside `Γ` is

  `K = {γ ∈ Γ : t⁻¹ γ t ∈ Γ}`

(`compressedStabilizer`), and the orbit map `γK ↦ γtΓ` identifies `Γ/K` with the
`Γ`-orbit of `tΓ` inside `G/Γ`.  Well-definedness and injectivity are the *same*
computation read in the two directions -- `γ₁⁻¹γ₂ ∈ K` unfolds to
`(γ₁t)⁻¹(γ₂t) ∈ Γ` -- which is why no separate argument is needed for either.
Equivariance is associativity.

So `Γ/K` embeds `Γ`-equivariantly and injectively into `G/Γ`, and
`IsSoficAction.of_equivariant_injective` does the rest, after restricting the
acting group along `Γ.subtype` with `IsSoficAction.compHom`.

## Why the stabiliser is the compressing image

In the ascending HNN extension `⟨Γ, t | tγt⁻¹ = α(γ)⟩` one has `tΓt⁻¹ = α(Γ)`,
and `t⁻¹γt ∈ Γ` says exactly `γ ∈ tΓt⁻¹`.  So `K = α(Γ)` and the conclusion
reads `Γ ↷ Γ/α(Γ)` sofic.  That identification is isolated as
`compressedStabilizer_eq_of_conj`, which takes the conjugation description as a
hypothesis rather than rebuilding the HNN extension; the repository's own
version of the same fact, for the vertical model, is
`MarkedCompression.smul_tSite_eq_iff`.

## What is not claimed

Nothing here decides the open problem.  The implication runs the easy way:
soficity of the ambient coset action is the hypothesis, not the conclusion.  No
converse is proved and none is expected -- `Γ/α(Γ)` may be a single point (when
`α` is onto) while `G/Γ` is infinite.
-/

namespace GroupApproximation

universe u

variable {G : Type u} [Group G]

/-! ## The stabiliser of the witness site inside the base -/

/-- The stabiliser of the site `tΓ` inside `Γ`: those `γ ∈ Γ` with
`t⁻¹ γ t ∈ Γ`.  For an ascending HNN extension this is the image of the
compressing endomorphism. -/
def compressedStabilizer (Γ : Subgroup G) (t : G) : Subgroup Γ where
  carrier := {γ | t⁻¹ * (γ : G) * t ∈ Γ}
  one_mem' := by
    show t⁻¹ * ((1 : Γ) : G) * t ∈ Γ
    simp
  mul_mem' := by
    intro a b ha hb
    show t⁻¹ * ((a * b : Γ) : G) * t ∈ Γ
    have : t⁻¹ * ((a * b : Γ) : G) * t
        = (t⁻¹ * (a : G) * t) * (t⁻¹ * (b : G) * t) := by
      push_cast
      group
    rw [this]
    exact Γ.mul_mem ha hb
  inv_mem' := by
    intro a ha
    show t⁻¹ * ((a⁻¹ : Γ) : G) * t ∈ Γ
    have : t⁻¹ * ((a⁻¹ : Γ) : G) * t = (t⁻¹ * (a : G) * t)⁻¹ := by
      push_cast
      group
    rw [this]
    exact Γ.inv_mem ha

@[simp] theorem mem_compressedStabilizer_iff (Γ : Subgroup G) (t : G) (γ : Γ) :
    γ ∈ compressedStabilizer Γ t ↔ t⁻¹ * (γ : G) * t ∈ Γ := Iff.rfl

/-- **The stabiliser is the conjugate.**  Whenever a subgroup `A` is described
by the conjugation condition -- which for an ascending HNN extension is
`A = tΓt⁻¹ = α(Γ)` -- it is the compressed stabiliser. -/
theorem compressedStabilizer_eq_of_conj (Γ : Subgroup G) (t : G) (A : Subgroup G)
    (hA : ∀ g : G, g ∈ A ↔ t⁻¹ * g * t ∈ Γ) (γ : Γ) :
    γ ∈ compressedStabilizer Γ t ↔ (γ : G) ∈ A :=
  (hA _).symm

/-! ## The orbit map -/

section Embedding

variable (Γ : Subgroup G) (t : G)

/-- The defining computation, used in both directions: two elements of `Γ` are
congruent modulo the compressed stabiliser exactly when their translates of the
site agree. -/
theorem compressedStabilizer_rel_iff (a b : Γ) :
    a⁻¹ * b ∈ compressedStabilizer Γ t ↔ ((a : G) * t)⁻¹ * ((b : G) * t) ∈ Γ := by
  rw [mem_compressedStabilizer_iff]
  have : ((a : G) * t)⁻¹ * ((b : G) * t) = t⁻¹ * ((a⁻¹ * b : Γ) : G) * t := by
    push_cast
    group
  rw [this]

/-- The orbit map `γK ↦ γtΓ`, identifying `Γ/K` with the `Γ`-orbit of the site
`tΓ` inside `G/Γ`. -/
def siteEmbedding : Γ ⧸ compressedStabilizer Γ t → G ⧸ Γ :=
  Quotient.map' (fun γ : Γ => (γ : G) * t)
    (by
      intro a b hab
      have hab' : a⁻¹ * b ∈ compressedStabilizer Γ t :=
        QuotientGroup.leftRel_apply.mp hab
      exact QuotientGroup.leftRel_apply.mpr
        ((compressedStabilizer_rel_iff Γ t a b).mp hab'))

@[simp] theorem siteEmbedding_mk (γ : Γ) :
    siteEmbedding Γ t (QuotientGroup.mk γ) = QuotientGroup.mk ((γ : G) * t) :=
  rfl

theorem siteEmbedding_injective :
    Function.Injective (siteEmbedding Γ t) := by
  intro x y hxy
  induction x using QuotientGroup.induction_on with
  | H a =>
    induction y using QuotientGroup.induction_on with
    | H b =>
      rw [siteEmbedding_mk, siteEmbedding_mk] at hxy
      have hmem : ((a : G) * t)⁻¹ * ((b : G) * t) ∈ Γ :=
        (QuotientGroup.eq (s := Γ)).mp hxy
      exact (QuotientGroup.eq (s := compressedStabilizer Γ t)).mpr
        ((compressedStabilizer_rel_iff Γ t a b).mpr hmem)

theorem siteEmbedding_equivariant
    (γ : Γ) (x : Γ ⧸ compressedStabilizer Γ t) :
    siteEmbedding Γ t (γ • x) = (γ : G) • siteEmbedding Γ t x := by
  induction x using QuotientGroup.induction_on with
  | H a =>
    show siteEmbedding Γ t (QuotientGroup.mk (γ * a))
      = (γ : G) • QuotientGroup.mk ((a : G) * t)
    rw [siteEmbedding_mk]
    show (QuotientGroup.mk (((γ * a : Γ) : G) * t) : G ⧸ Γ)
      = QuotientGroup.mk ((γ : G) * ((a : G) * t))
    push_cast
    rw [mul_assoc]

end Embedding

/-! ## The descent -/

/-- **Proposition 1.1.**  Soficity of the ambient coset action descends to the
compressed subgroup: if `G ↷ G/Γ` is sofic then `Γ ↷ Γ/K` is sofic, where `K`
is the stabiliser of the site `tΓ` inside `Γ`.

For an ascending HNN extension, `K = α(Γ)`, so this reads: soficity of
`G ↷ G/Γ` forces soficity of `Γ ↷ Γ/α(Γ)`. -/
theorem isSoficAction_quotient_compressedStabilizer (Γ : Subgroup G) (t : G)
    (hG : IsSoficAction G (G ⧸ Γ)) :
    IsSoficAction Γ (Γ ⧸ compressedStabilizer Γ t) := by
  letI : MulAction Γ (G ⧸ Γ) := MulAction.compHom _ Γ.subtype
  have hres : IsSoficAction Γ (G ⧸ Γ) := IsSoficAction.compHom Γ.subtype hG
  refine IsSoficAction.of_equivariant_injective (siteEmbedding Γ t)
    (siteEmbedding_injective Γ t) ?_ hres
  intro γ x
  exact siteEmbedding_equivariant Γ t γ x

end GroupApproximation
