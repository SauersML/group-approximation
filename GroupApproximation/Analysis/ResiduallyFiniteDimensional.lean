import GroupApproximation.Analysis.ProperIsometryFromCompression
import Mathlib.Algebra.Star.Pi
import Mathlib.Data.Matrix.Composition
import Mathlib.LinearAlgebra.Matrix.SemiringInverse

/-!
# Residual finite-dimensionality, and its failure under proper compression

This file supplies the residual-finite-dimensional clause of the
maximal-algebra consequence of proper one-sided conjugation:

> `C*_max(G)` is not stably finite, has no faithful trace, and in particular
> is neither residually finite-dimensional nor MF.

The failure of stable finiteness and the absence of a faithful trace are
already machine checked in `Analysis/ProperIsometryFromCompression` and
`Analysis/MaximalCStarProperCompression`.  Residual finite-dimensionality
had no Lean counterpart at all; this file defines it and proves the
implication the remark uses, namely that a residually finite-dimensional
algebra is Dedekind finite — indeed stably finite — so that the strict
compression rules it out.  The MF clause is handled in
`Analysis/MaximalCStarParagraphEndpoint`.

## The definition

For a unital C⋆-algebra, *residual finite-dimensionality* is the standard
requirement that the finite-dimensional ⋆-representations separate points.
A finite-dimensional ⋆-representation is a ⋆-homomorphism into the algebra
of operators on a finite-dimensional Hilbert space, that is, into a matrix
algebra `Matrix (Fin n) (Fin n) ℂ`; no continuity clause is needed because
⋆-homomorphisms of C⋆-algebras are automatically contractive.  Both the
unital form (`IsResiduallyFiniteDimensional`, with `StarAlgHom`
representations) and the a priori weaker degenerate form
(`HasSeparatingFiniteDimensionalStarHoms`, with `NonUnitalStarAlgHom`
representations) are defined, and the obstruction below is proved for the
weaker one, hence for both.  Both are stated at the generality of the
repository's `FaithfulTracialState`: a complex ⋆-algebra `[Ring A]
[StarRing A] [Algebra ℂ A]`, which every `CStarAlgebra` instantiates.

`isResiduallyFiniteDimensional_iff_exists_injective_piMatrix` records the
equivalent "embeds into a product of matrix algebras" formulation.

## Main results

* `HasSeparatingFiniteDimensionalStarHoms.isDedekindFiniteMonoid`: a
  separating family of finite-dimensional representations forces Dedekind
  finiteness, because a matrix algebra is Dedekind finite and the corner cut
  out by the image of the unit inherits that.
* `IsResiduallyFiniteDimensional.isStablyFiniteRing`: the same argument in
  every matrix amplification.
* `ProperProjectionCompression.map_conjugate_eq_of_matrix`: a
  finite-dimensional representation cannot see a proper compression — it
  identifies the projection with its unitary conjugate.
* `ProperProjectionCompression.not_isResiduallyFiniteDimensional`: hence an
  algebra carrying proper projection-compression data is not residually
  finite-dimensional.
-/

set_option linter.unusedSectionVars false

namespace GroupApproximation

universe u v

section Defs

variable (A : Type u) [Ring A] [StarRing A] [Algebra ℂ A]

/-- **Residual finite-dimensionality.**  The finite-dimensional
⋆-representations of `A` separate points: every nonzero element survives some
unital ⋆-homomorphism into a matrix algebra.  For a unital C⋆-algebra this is
the standard definition, a finite-dimensional representation being exactly a
⋆-homomorphism into the operators on some `ℂ ^ n`. -/
def IsResiduallyFiniteDimensional : Prop :=
  ∀ a : A, a ≠ 0 → ∃ (n : ℕ) (π : A →⋆ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ), π a ≠ 0

/-- The variant of `IsResiduallyFiniteDimensional` in which the separating
finite-dimensional ⋆-homomorphisms are *not* required to be unital, i.e. the
representations are allowed to be degenerate.  It is a priori weaker, so the
obstructions proved for it below are correspondingly stronger. -/
def HasSeparatingFiniteDimensionalStarHoms : Prop :=
  ∀ a : A, a ≠ 0 → ∃ (n : ℕ) (π : A →⋆ₙₐ[ℂ] Matrix (Fin n) (Fin n) ℂ), π a ≠ 0

end Defs

section Product

variable {A : Type u} [Ring A] [StarRing A] [Algebra ℂ A]

/-- A family of finite-dimensional representations, assembled into a single
⋆-homomorphism into the product of the matrix algebras. -/
noncomputable def piMatrixStarAlgHom {I : Type v} {n : I → ℕ}
    (π : ∀ i, A →⋆ₐ[ℂ] Matrix (Fin (n i)) (Fin (n i)) ℂ) :
    A →⋆ₐ[ℂ] ∀ i, Matrix (Fin (n i)) (Fin (n i)) ℂ where
  toFun a := fun i ↦ π i a
  map_one' := funext fun i ↦ map_one (π i)
  map_mul' x y := funext fun i ↦ map_mul (π i) x y
  map_zero' := funext fun i ↦ map_zero (π i)
  map_add' x y := funext fun i ↦ map_add (π i) x y
  commutes' r := funext fun i ↦ AlgHomClass.commutes (π i) r
  map_star' x := funext fun i ↦ map_star (π i) x

@[simp] theorem piMatrixStarAlgHom_apply {I : Type v} {n : I → ℕ}
    (π : ∀ i, A →⋆ₐ[ℂ] Matrix (Fin (n i)) (Fin (n i)) ℂ) (a : A) (i : I) :
    piMatrixStarAlgHom π a i = π i a :=
  rfl

end Product

section ProductCharacterization

variable (A : Type u) [Ring A] [StarRing A] [Algebra ℂ A]

/-- The standard reformulation of residual finite-dimensionality: the algebra
embeds into a product of matrix algebras. -/
theorem isResiduallyFiniteDimensional_iff_exists_injective_piMatrix :
    IsResiduallyFiniteDimensional A ↔
      ∃ (I : Type u) (n : I → ℕ)
        (Φ : A →⋆ₐ[ℂ] ∀ i, Matrix (Fin (n i)) (Fin (n i)) ℂ),
        Function.Injective Φ := by
  constructor
  · intro h
    refine ⟨{a : A // a ≠ 0}, fun i ↦ (h i.1 i.2).choose,
      piMatrixStarAlgHom (fun i ↦ (h i.1 i.2).choose_spec.choose), ?_⟩
    intro x y hxy
    by_contra hne
    have hd : x - y ≠ 0 := sub_ne_zero_of_ne hne
    have hcoord : (h (x - y) hd).choose_spec.choose x
        = (h (x - y) hd).choose_spec.choose y :=
      congrFun hxy ⟨x - y, hd⟩
    exact (h (x - y) hd).choose_spec.choose_spec
      (by rw [map_sub, hcoord, sub_self])
  · rintro ⟨I, n, Φ, hΦ⟩ a ha
    have hΦa : Φ a ≠ 0 := by
      intro h0
      exact ha (hΦ (by rw [h0, map_zero]))
    have hcoord : ∃ i, Φ a i ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hΦa (funext hall)
    obtain ⟨i, hi⟩ := hcoord
    exact ⟨n i, (Pi.evalStarAlgHom ℂ (fun j ↦ Matrix (Fin (n j)) (Fin (n j)) ℂ) i).comp Φ,
      hi⟩

end ProductCharacterization

section Finiteness

variable {A : Type u} [Ring A] [StarRing A] [Algebra ℂ A]

/-- A unital finite-dimensional representation is in particular a possibly
degenerate one. -/
theorem IsResiduallyFiniteDimensional.hasSeparatingFiniteDimensionalStarHoms
    (h : IsResiduallyFiniteDimensional A) :
    HasSeparatingFiniteDimensionalStarHoms A := by
  intro a ha
  obtain ⟨n, π, hπ⟩ := h a ha
  refine ⟨n, π.toNonUnitalStarAlgHom, ?_⟩
  simpa using hπ

/-- **A separating family of finite-dimensional representations forces
Dedekind finiteness.**  A matrix algebra is Dedekind finite, and a one-sided
inverse in `A` is carried by each representation into the corner cut out by
the image of the unit, where the complement correction `x + (1 - π 1)` turns
it into a genuine one-sided inverse of the matrix algebra.  Dedekind
finiteness there reverses it, so the defect `b * a - 1` is killed by every
representation, hence is zero. -/
theorem HasSeparatingFiniteDimensionalStarHoms.isDedekindFiniteMonoid
    (h : HasSeparatingFiniteDimensionalStarHoms A) : IsDedekindFiniteMonoid A where
  mul_eq_one_symm := by
    intro a b hab
    by_contra hne
    obtain ⟨n, π, hπ⟩ := h (b * a - 1) (sub_ne_zero_of_ne hne)
    have hpp : π 1 * π 1 = π (1 : A) := by rw [← map_mul, one_mul]
    have hpa : π 1 * π a = π a := by rw [← map_mul, one_mul]
    have hap : π a * π 1 = π a := by rw [← map_mul, mul_one]
    have hpb : π 1 * π b = π b := by rw [← map_mul, one_mul]
    have hbp : π b * π 1 = π b := by rw [← map_mul, mul_one]
    have hab' : π a * π b = π (1 : A) := by rw [← map_mul, hab]
    have hcompl : (1 - π 1) * (1 - π 1) = 1 - π 1 := by
      have hexp : (1 - π 1) * (1 - π 1) = 1 - π 1 - π 1 + π 1 * π 1 := by
        noncomm_ring
      rw [hexp, hpp]
      noncomm_ring
    have ha0 : π a * (1 - π 1) = 0 := by
      have hexp : π a * (1 - π 1) = π a - π a * π 1 := by noncomm_ring
      rw [hexp, hap, sub_self]
    have hb0 : (1 - π 1) * π b = 0 := by
      have hexp : (1 - π 1) * π b = π b - π 1 * π b := by noncomm_ring
      rw [hexp, hpb, sub_self]
    have ha0' : π b * (1 - π 1) = 0 := by
      have hexp : π b * (1 - π 1) = π b - π b * π 1 := by noncomm_ring
      rw [hexp, hbp, sub_self]
    have hb0' : (1 - π 1) * π a = 0 := by
      have hexp : (1 - π 1) * π a = π a - π 1 * π a := by noncomm_ring
      rw [hexp, hpa, sub_self]
    have hprod : (π a + (1 - π 1)) * (π b + (1 - π 1)) = 1 := by
      have hexp : (π a + (1 - π 1)) * (π b + (1 - π 1))
          = π a * π b + π a * (1 - π 1) + ((1 - π 1) * π b + (1 - π 1) * (1 - π 1)) := by
        noncomm_ring
      rw [hexp, ha0, hb0, hcompl, hab']
      noncomm_ring
    have hrev : (π b + (1 - π 1)) * (π a + (1 - π 1)) = 1 :=
      mul_eq_one_symm hprod
    have hexp2 : (π b + (1 - π 1)) * (π a + (1 - π 1))
        = π b * π a + π b * (1 - π 1) + ((1 - π 1) * π a + (1 - π 1) * (1 - π 1)) := by
      noncomm_ring
    rw [hexp2, ha0', hb0', hcompl, add_zero, zero_add] at hrev
    have hba : π b * π a = π (1 : A) := by
      have hsub := eq_sub_of_add_eq hrev
      rwa [sub_sub_cancel] at hsub
    exact hπ (by rw [map_sub, map_mul, hba, sub_self])

/-- A residually finite-dimensional algebra is Dedekind finite. -/
theorem IsResiduallyFiniteDimensional.isDedekindFiniteMonoid
    (h : IsResiduallyFiniteDimensional A) : IsDedekindFiniteMonoid A :=
  h.hasSeparatingFiniteDimensionalStarHoms.isDedekindFiniteMonoid

/-- **A residually finite-dimensional algebra is stably finite.**  Applying a
separating representation entrywise turns a one-sided inverse in an
amplification `Matrix (Fin k) (Fin k) A` into one in
`Matrix (Fin k) (Fin k) (Matrix (Fin n) (Fin n) ℂ)`, which is Dedekind
finite; so every entry of the defect `N * M - 1` is killed by some
representation, hence vanishes. -/
theorem IsResiduallyFiniteDimensional.isStablyFiniteRing
    (h : IsResiduallyFiniteDimensional A) : IsStablyFiniteRing A where
  isDedekindFiniteMonoid k := by
    constructor
    intro M N hMN
    by_contra hne
    obtain ⟨i, j, hij⟩ :
        ∃ i j, (N * M) i j ≠ (1 : Matrix (Fin k) (Fin k) A) i j := by
      by_contra hall
      push Not at hall
      exact hne (by ext i j; exact hall i j)
    obtain ⟨n, π, hπ⟩ := h _ (sub_ne_zero_of_ne hij)
    have hmapMul : ∀ P Q : Matrix (Fin k) (Fin k) A,
        (P * Q).map π = P.map π * Q.map π :=
      fun _ _ ↦ Matrix.map_mul (f := π)
    have hmapOne : (1 : Matrix (Fin k) (Fin k) A).map π = 1 :=
      Matrix.map_one _ (map_zero π) (map_one π)
    have h1 : M.map π * N.map π = 1 := by
      rw [← hmapMul, hMN, hmapOne]
    have h2 : N.map π * M.map π = 1 := mul_eq_one_symm h1
    have h3 : (N * M).map π = (1 : Matrix (Fin k) (Fin k) A).map π := by
      rw [hmapMul, h2, hmapOne]
    have h4 : π ((N * M) i j) = π ((1 : Matrix (Fin k) (Fin k) A) i j) := by
      simpa only [Matrix.map_apply] using
        congrArg
          (fun T : Matrix (Fin k) (Fin k) (Matrix (Fin n) (Fin n) ℂ) ↦ T i j) h3
    exact hπ (by rw [map_sub, h4, sub_self])

end Finiteness

namespace ProperProjectionCompression

variable {A : Type u} [Ring A] [StarRing A] [Algebra ℂ A]

/-- **A finite-dimensional representation cannot see a proper compression.**
The image of a proper projection compression under a unital ⋆-homomorphism
into a matrix algebra has the projection equal to its unitary conjugate:
matrix algebras are Dedekind finite, and in a Dedekind finite ⋆-ring a
projection absorbed by a unitary conjugate of itself equals it.  This is the
finite-dimensional counterpart of the manuscript's invariant-size
principle. -/
theorem map_conjugate_eq_of_matrix (D : ProperProjectionCompression A) {n : ℕ}
    (π : A →⋆ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ) :
    π (D.u * D.p * star D.u) = π D.p := by
  have hp_star : star (π D.p) = π D.p := by rw [← map_star, D.p_star]
  have hp_mul : π D.p * π D.p = π D.p := by rw [← map_mul, D.p_mul_p]
  have hu_star_mul : star (π D.u) * π D.u = 1 := by
    rw [← map_star, ← map_mul, D.u_star_mul, map_one]
  have hu_mul_star : π D.u * star (π D.u) = 1 := by
    rw [← map_star, ← map_mul, D.u_mul_star, map_one]
  have habs_left : π D.p * (π D.u * π D.p * star (π D.u)) = π D.p := by
    rw [← map_star, ← map_mul, ← map_mul, ← map_mul, D.p_mul_conjugate]
  have habs_right : (π D.u * π D.p * star (π D.u)) * π D.p = π D.p := by
    rw [← map_star, ← map_mul, ← map_mul, ← map_mul, D.conjugate_mul_p]
  have hfix := unitary_conjugate_eq_of_absorbs hp_star hp_mul hu_star_mul
    hu_mul_star habs_left habs_right
  rw [← map_star, ← map_mul, ← map_mul] at hfix
  exact hfix

/-- Proper projection-compression data rules out any separating family of
finite-dimensional representations, degenerate ones included. -/
theorem not_hasSeparatingFiniteDimensionalStarHoms
    (D : ProperProjectionCompression A) :
    ¬ HasSeparatingFiniteDimensionalStarHoms A := fun h ↦
  D.not_isDedekindFiniteMonoid h.isDedekindFiniteMonoid

/-- **An algebra carrying a proper projection compression is not residually
finite-dimensional.**  This is the manuscript's "in particular": the
compression destroys Dedekind finiteness, and residual finite-dimensionality
would restore it. -/
theorem not_isResiduallyFiniteDimensional (D : ProperProjectionCompression A) :
    ¬ IsResiduallyFiniteDimensional A := fun h ↦
  D.not_isDedekindFiniteMonoid h.isDedekindFiniteMonoid

/-- The same conclusion read off directly from the mechanism: the properness
witness `u p u⋆ ≠ p` is a nonzero element that every finite-dimensional
representation annihilates. -/
theorem not_isResiduallyFiniteDimensional_of_conjugate_ne
    (D : ProperProjectionCompression A) :
    ¬ IsResiduallyFiniteDimensional A := by
  intro h
  obtain ⟨n, π, hπ⟩ := h (D.u * D.p * star D.u - D.p)
    (sub_ne_zero_of_ne D.conjugate_ne)
  exact hπ (by rw [map_sub, D.map_conjugate_eq_of_matrix π, sub_self])

end ProperProjectionCompression

end GroupApproximation
