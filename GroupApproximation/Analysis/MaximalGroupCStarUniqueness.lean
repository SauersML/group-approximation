import GroupApproximation.Analysis.MaximalGroupCStar

/-!
# "The" maximal group C-star algebra: what the definite article is worth

The audit item behind this file (`PRE.19`) recorded that the development
proves a *universe-relative* universal construction while the manuscript spoke
of "the maximal group C-star algebra" without an identification theorem, and
asked for one of two repairs: formalize an equivalence across universes, or
keep every formal claim explicitly universe-relative.

As of 2026-08-16 the manuscript has taken the second, in print.
`prop:maximal-cstar` now reads

> The canonical map `h ↦ u_h` is injective, and for every unital `C*`-algebra
> `B` **lying in a fixed universe that contains `H`**, and every homomorphism
> `ρ : H → U(B)`, there is a unique unital `*`-homomorphism `C*_max(H) → B`
> with `u_h ↦ ρ(h)` for every `h ∈ H`.

with the prose after it adding that "the restriction on `B` is what keeps *all
representations* a set rather than a proper class; it costs nothing, since
every target used in this paper is small, and it is the form the accompanying
development quantifies over".  That is a literal match for the badged
`manuscriptUniverseRelativeMaximalGroupCStar`, whose targets are exactly the
`B : Type u` for `G : Type u`, and the audit row is answered by the manuscript
rather than by Lean.

What remains, and what this file supplies, is the reason the *definite
article* is legitimate under that restriction: a fixed universe pins the
algebra down.

## What is proved

`starAlgEquiv_of_universalProperty`: any two unital C-star algebras in
`Type u` that satisfy the printed universal property for `Type u` targets are
canonically ⋆-isomorphic, by an isomorphism carrying one canonical unitary
representation to the other.  This is the initial-object argument — each
mediates through the other, and both composites agree with the identity by the
uniqueness half — and it is what justifies the definite article: at a fixed
universe, the printed universal property determines the algebra up to a unique
⋆-isomorphism over `G`.

## What is not proved, and why not

The construction `MaximalGroupCStar G` for `G : Type u` lives in
`Type (u + 1)`, because it is a subalgebra of a product indexed by a *set* of
representations, while its universal property
(`manuscriptUniverseRelativeMaximalGroupCStar`) quantifies over targets in
`Type u`.  So `MaximalGroupCStar G` is not itself an instance of the theorem
below: to feed it to its own universal property as a target one would need it
in `Type u`, and it is one universe too big.

That gap is not a missing lemma, it is the universe relativity itself, and no
`Type u`-target universal property can close it.  Which is why the first of
the audit's two repair options was never the live one, and why the manuscript
adopting the second — printing the restriction on `B` in the statement of
`prop:maximal-cstar` rather than in a parenthetical afterwards — is the
correct resolution rather than a concession.  What this file adds is that the
resolution costs nothing: the printed universal property *does* pin the
algebra down, at each universe, so "the" is a definite description and not an
abuse.
-/

namespace GroupApproximation
namespace MaximalGroupCStarUniqueness

universe u

/-- **The printed universal property determines the algebra.**  Two unital
C-star algebras carrying a unitary representation of `G` through which every
unitary representation of `G` on a same-universe C-star algebra factors
uniquely are ⋆-isomorphic, by an isomorphism matching the two canonical
representations.

This is the initial-object argument: `f` mediates `A₁ → A₂` and `g` mediates
`A₂ → A₁`, so `g ∘ f` mediates `A₁ → A₁`; the identity does too, and the
uniqueness half of `h₁` at `A₁` forces them equal.  Symmetrically for
`f ∘ g`. -/
theorem starAlgEquiv_of_universalProperty
    (G : Type u) [Group G]
    {A₁ : Type u} [CStarAlgebra A₁] (iota₁ : G →* unitary A₁)
    {A₂ : Type u} [CStarAlgebra A₂] (iota₂ : G →* unitary A₂)
    (h₁ : ∀ (B : Type u) [CStarAlgebra B] (rho : G →* unitary B),
      ∃! f : A₁ →⋆ₐ[ℂ] B, ∀ g : G, f (iota₁ g : A₁) = (rho g : B))
    (h₂ : ∀ (B : Type u) [CStarAlgebra B] (rho : G →* unitary B),
      ∃! f : A₂ →⋆ₐ[ℂ] B, ∀ g : G, f (iota₂ g : A₂) = (rho g : B)) :
    ∃ e : A₁ ≃⋆ₐ[ℂ] A₂, ∀ g : G, e (iota₁ g : A₁) = (iota₂ g : A₂) := by
  obtain ⟨f, hf, -⟩ := h₁ A₂ iota₂
  obtain ⟨g, hg, -⟩ := h₂ A₁ iota₁
  -- The uniqueness half is a statement *about* the witness, so the witness has
  -- to be kept rather than cleared: `⟨-, -, huniq⟩` would discard the very
  -- thing `huniq`'s type mentions.
  obtain ⟨w₁, -, huniq₁⟩ := h₁ A₁ iota₁
  obtain ⟨w₂, -, huniq₂⟩ := h₂ A₂ iota₂
  have hgf : g.comp f = StarAlgHom.id ℂ A₁ := by
    have hcomp : ∀ x : G, (g.comp f) (iota₁ x : A₁) = (iota₁ x : A₁) := by
      intro x
      show g (f (iota₁ x : A₁)) = (iota₁ x : A₁)
      rw [hf x, hg x]
    have hid : ∀ x : G,
        (StarAlgHom.id ℂ A₁) (iota₁ x : A₁) = (iota₁ x : A₁) := fun _ ↦ rfl
    exact (huniq₁ _ hcomp).trans (huniq₁ _ hid).symm
  have hfg : f.comp g = StarAlgHom.id ℂ A₂ := by
    have hcomp : ∀ x : G, (f.comp g) (iota₂ x : A₂) = (iota₂ x : A₂) := by
      intro x
      show f (g (iota₂ x : A₂)) = (iota₂ x : A₂)
      rw [hg x, hf x]
    have hid : ∀ x : G,
        (StarAlgHom.id ℂ A₂) (iota₂ x : A₂) = (iota₂ x : A₂) := fun _ ↦ rfl
    exact (huniq₂ _ hcomp).trans (huniq₂ _ hid).symm
  refine ⟨StarAlgEquiv.ofStarAlgHom f g hgf hfg, fun x ↦ ?_⟩
  simpa using hf x

end MaximalGroupCStarUniqueness
end GroupApproximation
