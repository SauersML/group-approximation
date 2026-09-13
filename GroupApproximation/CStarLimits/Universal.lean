import GroupApproximation.CStarLimits.Envelope
import GroupApproximation.CStarLimits.FreeStar

/-!
# Universal C⋆-algebras from generators and norm-bounded relations

Let `X` be a set of generators.  A *norm-bounded relation* is a pair `(a, c)` with `a` in the free
⋆-algebra `FreeStarAlgebra X` and `c : ℝ≥0`, standing for `‖a‖ ≤ c`.  The relation `a = 0` is
the pair `(a, 0)`.  Let `P` be a set of relations.  A family `g : X → B` in a unital C⋆-algebra
*satisfies* `P` if the induced ⋆-homomorphism `FreeStarAlgebra.lift g` satisfies every
relation.  Suppose every generator is norm-bounded over all families satisfying `P`.  Then the
*universal C⋆-algebra* `UnivCStar P hP` exists.  It carries generators `univGen P hP x`
satisfying the relations, and every family satisfying `P` factors uniquely through it.

## Main results

- `isBounded_of_gen`: boundedness only has to be checked on the generators.
  `isBounded_of_isometry_rel` and `isBounded_of_idem_rel` give it for families of isometries
  and of partial isometries.
- `UnivCStar`, `univGen`, `norm_univ_rel`: the universal C⋆-algebra and its generators, which
  satisfy the relations.
- `univLift`, `univLift_univGen`, `univ_hom_ext`, `existsUnique_univLift`: the universal property,
  for targets in every universe.

## References

- Blackadar, *Operator Algebras*, II.8.3.
- Loring, *Lifting Solutions to Perturbing Problems in C⋆-Algebras*, Ch. 3.
-/

namespace GroupApproximation
namespace CStarLimits

open scoped NNReal
open FreeStarAlgebra (gen)

noncomputable section

universe u v

variable {X : Type u}

/-- Norm-bounded relations on the generators `X`. -/
abbrev Relations (X : Type u) : Type u := Set (FreeStarAlgebra X × ℝ≥0)

variable (P : Relations X)

/-- **Boundedness is checked on the generators.** -/
theorem isBounded_of_gen (h : ∀ x : X, IsBoundedElem P (gen x)) : IsBounded P :=
  isBounded_of_adjoin P FreeStarAlgebra.adjoin_gen fun s hs ↦ by
    rcases hs with ⟨x, rfl⟩ | ⟨x, rfl⟩
    · exact h x
    · exact isBoundedElem_star P (h x)

/-- A family of isometries: every generator is subject to `star (gen x) * gen x = 1`. -/
theorem isBounded_of_isometry_rel
    (h : ∀ x : X, (star (gen x) * gen x - 1, (0 : ℝ≥0)) ∈ P) : IsBounded P :=
  isBounded_of_gen P fun x ↦ isBoundedElem_of_isometry_rel P (h x)

/-- A family of partial isometries: every generator is subject to
`(star (gen x) * gen x)² = star (gen x) * gen x`. -/
theorem isBounded_of_idem_rel
    (h : ∀ x : X, ((star (gen x) * gen x) * (star (gen x) * gen x) - star (gen x) * gen x,
      (0 : ℝ≥0)) ∈ P) : IsBounded P :=
  isBounded_of_gen P fun x ↦ isBoundedElem_of_idem_rel P (h x)

/-- **The universal C⋆-algebra** on the generators `X` with relations `P`. -/
abbrev UnivCStar (hP : IsBounded P) : Type u := Envelope P hP

/-- The generators of the universal C⋆-algebra. -/
def univGen (hP : IsBounded P) (x : X) : UnivCStar P hP := envHom P hP (gen x)

/-- Evaluating free ⋆-polynomials at the universal generators is the canonical map. -/
theorem lift_univGen (hP : IsBounded P) : FreeStarAlgebra.lift (univGen P hP) = envHom P hP :=
  FreeStarAlgebra.hom_ext fun x ↦ FreeStarAlgebra.lift_gen (univGen P hP) x

/-- **The universal generators satisfy the relations.** -/
theorem norm_univ_rel (hP : IsBounded P) {p : FreeStarAlgebra X × ℝ≥0} (hp : p ∈ P) :
    ‖FreeStarAlgebra.lift (univGen P hP) p.1‖ ≤ p.2 := by
  rw [lift_univGen]
  exact norm_envHom_rel P hP hp

variable {P}

/-- **The universal property.**  A family in a C⋆-algebra in any universe that satisfies the
relations extends to a ⋆-homomorphism out of the universal C⋆-algebra. -/
def univLift (hP : IsBounded P) {B : Type v} [CStarAlgebra B] (g : X → B)
    (hg : ∀ p : FreeStarAlgebra X × ℝ≥0, p ∈ P → ‖FreeStarAlgebra.lift g p.1‖ ≤ p.2) :
    UnivCStar P hP →⋆ₐ[ℂ] B :=
  envLift hP (FreeStarAlgebra.lift g) hg

@[simp] theorem univLift_univGen (hP : IsBounded P) {B : Type v} [CStarAlgebra B] (g : X → B)
    (hg : ∀ p : FreeStarAlgebra X × ℝ≥0, p ∈ P → ‖FreeStarAlgebra.lift g p.1‖ ≤ p.2) (x : X) :
    univLift hP g hg (univGen P hP x) = g x :=
  (envLift_envHom hP (FreeStarAlgebra.lift g) hg (gen x)).trans (FreeStarAlgebra.lift_gen g x)

/-- ⋆-homomorphisms out of the universal C⋆-algebra are determined on the generators. -/
theorem univ_hom_ext (hP : IsBounded P) {B : Type v} [CStarAlgebra B]
    {F₁ F₂ : UnivCStar P hP →⋆ₐ[ℂ] B} (h : ∀ x, F₁ (univGen P hP x) = F₂ (univGen P hP x)) :
    F₁ = F₂ := by
  have hc : F₁.comp (envHom P hP) = F₂.comp (envHom P hP) :=
    FreeStarAlgebra.hom_ext fun x ↦ by
      rw [StarAlgHom.comp_apply, StarAlgHom.comp_apply]
      exact h x
  exact envHom_ext hP fun a ↦ by simpa only [StarAlgHom.comp_apply] using DFunLike.congr_fun hc a

/-- Existence and uniqueness of the extension through the universal C⋆-algebra. -/
theorem existsUnique_univLift (hP : IsBounded P) {B : Type v} [CStarAlgebra B] (g : X → B)
    (hg : ∀ p : FreeStarAlgebra X × ℝ≥0, p ∈ P → ‖FreeStarAlgebra.lift g p.1‖ ≤ p.2) :
    ∃! F : UnivCStar P hP →⋆ₐ[ℂ] B, ∀ x, F (univGen P hP x) = g x :=
  ⟨univLift hP g hg, univLift_univGen hP g hg, fun F hF ↦
    univ_hom_ext hP fun x ↦ by rw [hF x, univLift_univGen]⟩

end

end CStarLimits
end GroupApproximation
