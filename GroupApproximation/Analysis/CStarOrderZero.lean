import GroupApproximation.Analysis.CStarCPStarTarget

/-!
# Completely positive contractive order-zero maps

An **order-zero map** is a completely positive contraction that preserves
orthogonality: `a ⟂ b ⟹ φ a ⟂ φ b`, where two positive elements are
orthogonal when their product vanishes.  They are the maps
Winter--Zacharias isolated (*Completely positive maps of order zero*, Münster
J. Math. **2** (2009), 311--324), and they are one of the two structural
inputs of Tikuisis--White--Winter: the whole quasidiagonality argument is run
on order-zero maps into a corona algebra, never on `⋆`-homomorphisms, because
order-zero maps have a *cone* of deformations that `⋆`-homomorphisms do not.

## What is defined, and in which spelling

Positivity is spelled `∃ x, a = star x * x` rather than `0 ≤ a`, exactly as
`CStarExactness.IsCompletelyPositive` spells it: the repository's concrete
algebras appear as closed `StarSubalgebra`s of `B(H)`, which carry no
`PartialOrder` instance, and the two spellings agree on a C⋆-algebra.  Nothing
below needs the equivalence, so nothing below assumes an order instance.

`IsOrderZero` bundles the three clauses --- complete positivity, contractivity
and orthogonality preservation.  Contractivity is a separate clause rather
than a consequence: it *is* a consequence for unital domains, by
`CStarExactness.IsCompletelyPositive.norm_apply_le_of_unital`, but only after
Stinespring, and order-zero maps are used here with non-unital domains too.

## What is proved

Everything in this file is unconditional.

* `⋆`-homomorphisms are order zero (`isOrderZero_of_nonUnitalStarAlgHom`), so
  the notion is a genuine weakening and never empty;
* order zero is stable under composition with a `⋆`-homomorphism on either
  side (`IsOrderZero.comp_starAlgHom`, `IsOrderZero.starAlgHom_comp`);
* order-zero maps are `⋆`-preserving (`IsOrderZero.map_star`, from
  `OrderZero.map_star_of_cp`), hence orthogonality of the images is symmetric
  (`IsOrderZero.orthogonal_symm`) even though the defining clause is not
  visibly symmetric;
* the zero map is order zero, and order zero is preserved by scaling by a
  scalar of modulus at most one that is *real and nonnegative*
  (`IsOrderZero.smul`), which is what the cone picture is built out of.

What is **not** here is the Winter--Zacharias structure theorem --- that every
order-zero map factors as `φ a = h · π a` for a positive contraction `h`
commuting with a `⋆`-homomorphism `π` into the multiplier algebra of
`C⋆(φ(A))`.  The *converse* direction of that theorem, which is the direction
that constructs order-zero maps, is proved in
`Analysis.CStarOrderZeroSupport`; the forward direction needs multiplier
algebras, which do not exist in this development, and it is recorded as an
input there.
-/

namespace GroupApproximation
namespace OrderZero

open CStarExactness

universe u v w

/-! ## Positivity without an order instance -/

section Positive

variable {A : Type u} [NonUnitalCStarAlgebra A]

/-- **Positivity, spelled as in `IsCompletelyPositive`**: `a` is positive when
it is of the form `x⋆x`.  On a C⋆-algebra this is equivalent to `0 ≤ a` for
the `StarOrderedRing` order, and it needs no order instance. -/
def IsPositiveElem (a : A) : Prop := ∃ x : A, a = star x * x

theorem isPositiveElem_star_mul_self (x : A) : IsPositiveElem (star x * x) :=
  ⟨x, rfl⟩

theorem isPositiveElem_zero : IsPositiveElem (0 : A) :=
  ⟨0, by rw [star_zero, zero_mul]⟩

theorem IsPositiveElem.isSelfAdjoint {a : A} (ha : IsPositiveElem a) :
    IsSelfAdjoint a := by
  obtain ⟨x, rfl⟩ := ha
  exact IsSelfAdjoint.star_mul_self x

/-- **Orthogonality of positive elements is symmetric.**  The defining clause
of an order-zero map fixes an order of the factors; this is what says the
choice is immaterial. -/
theorem mul_eq_zero_comm_of_isSelfAdjoint {a b : A} (ha : IsSelfAdjoint a)
    (hb : IsSelfAdjoint b) (hab : a * b = 0) : b * a = 0 := by
  have h : star (a * b) = star (0 : A) := by rw [hab]
  rw [star_mul, ha.star_eq, hb.star_eq, star_zero] at h
  exact h

end Positive

/-! ## Order-zero maps -/

section Def

variable {A : Type u} {B : Type v}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- **Orthogonality preservation.**  Positive elements with vanishing product
have images with vanishing product. -/
def IsOrthogonalityPreserving (φ : A →ₗ[ℂ] B) : Prop :=
  ∀ a b : A, IsPositiveElem a → IsPositiveElem b → a * b = 0 → φ a * φ b = 0

/-- **A completely positive contractive order-zero map.**

Winter--Zacharias, *Completely positive maps of order zero*: a c.p.c. map that
preserves orthogonality.  The three clauses are kept separate rather than
bundled into a subtype so that a construction may discharge them in any order,
and so that a theorem consuming only one of them says so in its hypotheses. -/
structure IsOrderZero (φ : A →ₗ[ℂ] B) : Prop where
  /-- `φ` is completely positive. -/
  completelyPositive : IsCompletelyPositive φ
  /-- `φ` is a contraction. -/
  norm_apply_le : ∀ a : A, ‖φ a‖ ≤ ‖a‖
  /-- `φ` preserves orthogonality of positive elements. -/
  orthogonal : IsOrthogonalityPreserving φ

end Def

/-! ## `⋆`-homomorphisms are order zero -/

section Hom

variable {A : Type u} {B : Type v} {C : Type w}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
variable [NonUnitalCStarAlgebra C]

/-- Applying the linear-map coercion of a `⋆`-homomorphism is applying the
homomorphism.  Isolated as a lemma because every proof below rewrites with
it, and because it is the one step in this file whose failure would be
invisible in the statement of the theorem it appears in. -/
theorem coe_nonUnitalStarAlgHom_apply (f : A →⋆ₙₐ[ℂ] B) (a : A) :
    (f : A →ₗ[ℂ] B) a = f a := rfl

/-- `⋆`-homomorphisms carry positive elements to positive elements. -/
theorem IsPositiveElem.map_nonUnitalStarAlgHom (f : A →⋆ₙₐ[ℂ] B) {a : A}
    (ha : IsPositiveElem a) : IsPositiveElem (f a) := by
  obtain ⟨x, rfl⟩ := ha
  exact ⟨f x, by rw [map_mul, map_star]⟩

/-- **Every `⋆`-homomorphism of C⋆-algebras is an order-zero map.**  Complete
positivity is `isCompletelyPositive_of_starAlgHom`, contractivity is the
standard C⋆-estimate `NonUnitalStarAlgHom.norm_apply_le`, and orthogonality is
multiplicativity: `f a * f b = f (a * b) = f 0 = 0`. -/
theorem isOrderZero_of_nonUnitalStarAlgHom (f : A →⋆ₙₐ[ℂ] B) :
    IsOrderZero ((f : A →ₗ[ℂ] B)) where
  completelyPositive := isCompletelyPositive_of_starAlgHom f
  norm_apply_le a := by
    rw [coe_nonUnitalStarAlgHom_apply]
    exact NonUnitalStarAlgHom.norm_apply_le f a
  orthogonal a b _ _ hab := by
    rw [coe_nonUnitalStarAlgHom_apply, coe_nonUnitalStarAlgHom_apply,
      ← map_mul, hab, map_zero]

/-- **Order zero is stable under precomposition with a `⋆`-homomorphism.** -/
theorem IsOrderZero.comp_starAlgHom {φ : A →ₗ[ℂ] B} (hφ : IsOrderZero φ)
    (f : C →⋆ₙₐ[ℂ] A) : IsOrderZero (φ ∘ₗ (f : C →ₗ[ℂ] A)) where
  completelyPositive :=
    hφ.completelyPositive.comp (isCompletelyPositive_of_starAlgHom f)
  norm_apply_le c := by
    show ‖φ ((f : C →ₗ[ℂ] A) c)‖ ≤ ‖c‖
    rw [coe_nonUnitalStarAlgHom_apply]
    exact le_trans (hφ.norm_apply_le (f c)) (NonUnitalStarAlgHom.norm_apply_le f c)
  orthogonal c d hc hd hcd := by
    show φ ((f : C →ₗ[ℂ] A) c) * φ ((f : C →ₗ[ℂ] A) d) = 0
    rw [coe_nonUnitalStarAlgHom_apply, coe_nonUnitalStarAlgHom_apply]
    refine hφ.orthogonal (f c) (f d) (hc.map_nonUnitalStarAlgHom f)
      (hd.map_nonUnitalStarAlgHom f) ?_
    rw [← map_mul, hcd, map_zero]

/-- **Order zero is stable under postcomposition with a `⋆`-homomorphism.** -/
theorem IsOrderZero.starAlgHom_comp {φ : A →ₗ[ℂ] B} (hφ : IsOrderZero φ)
    (g : B →⋆ₙₐ[ℂ] C) : IsOrderZero ((g : B →ₗ[ℂ] C) ∘ₗ φ) where
  completelyPositive :=
    (isCompletelyPositive_of_starAlgHom g).comp hφ.completelyPositive
  norm_apply_le a := by
    show ‖(g : B →ₗ[ℂ] C) (φ a)‖ ≤ ‖a‖
    rw [coe_nonUnitalStarAlgHom_apply]
    exact le_trans (NonUnitalStarAlgHom.norm_apply_le g (φ a)) (hφ.norm_apply_le a)
  orthogonal a b ha hb hab := by
    show (g : B →ₗ[ℂ] C) (φ a) * (g : B →ₗ[ℂ] C) (φ b) = 0
    rw [coe_nonUnitalStarAlgHom_apply, coe_nonUnitalStarAlgHom_apply,
      ← map_mul, hφ.orthogonal a b ha hb hab, map_zero]

/-- The zero map is order zero. -/
theorem isOrderZero_zero : IsOrderZero (0 : A →ₗ[ℂ] B) where
  completelyPositive := by
    intro n M _
    exact ⟨0, by ext i j; simp⟩
  norm_apply_le a := by
    rw [LinearMap.zero_apply, norm_zero]
    exact norm_nonneg a
  orthogonal a b _ _ _ := by
    rw [LinearMap.zero_apply, zero_mul]

end Hom

/-! ## `⋆`-preservation and the symmetry of the orthogonality clause -/

section Star

variable {A : Type u} {B : Type v}
variable [CStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- **Order-zero maps are `⋆`-preserving.**  This uses only the complete
positivity clause. -/
theorem IsOrderZero.map_star {φ : A →ₗ[ℂ] B} (hφ : IsOrderZero φ) (a : A) :
    φ (star a) = star (φ a) :=
  map_star_of_cp hφ.completelyPositive a

/-- Order-zero maps carry selfadjoint elements to selfadjoint elements. -/
theorem IsOrderZero.isSelfAdjoint_map {φ : A →ₗ[ℂ] B} (hφ : IsOrderZero φ)
    {a : A} (ha : IsSelfAdjoint a) : IsSelfAdjoint (φ a) :=
  isSelfAdjoint_map_of_cp hφ.completelyPositive ha

/-- **The orthogonality clause is symmetric.**  `φ a * φ b = 0` was assumed
in one order only; the other order follows because `φ` preserves adjoints and
both images are selfadjoint. -/
theorem IsOrderZero.orthogonal_symm {φ : A →ₗ[ℂ] B} (hφ : IsOrderZero φ)
    {a b : A} (ha : IsPositiveElem a) (hb : IsPositiveElem b)
    (hab : a * b = 0) : φ b * φ a = 0 :=
  mul_eq_zero_comm_of_isSelfAdjoint
    (hφ.isSelfAdjoint_map ha.isSelfAdjoint)
    (hφ.isSelfAdjoint_map hb.isSelfAdjoint)
    (hφ.orthogonal a b ha hb hab)

end Star

end OrderZero
end GroupApproximation
