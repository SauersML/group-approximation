import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Analysis.Complex.Basic

/-!
# The free complex ⋆-algebra on a set of generators

`FreeStarAlgebra X` is the free unital complex ⋆-algebra on generators `gen x`, `x : X`, with a
conjugate-linear involution.  It is the monoid algebra over `ℂ` of the free monoid on the letters
`X ⊕ X`: the letter `inl x` stands for `gen x` and `inr x` for `star (gen x)`.  The involution
conjugates the coefficients and sends a word to its reverse with every letter swapped.

Mathlib's `FreeAlgebra` carries a star only with trivial action on the scalars, so it is not a
complex ⋆-algebra in the operator-algebra sense.  This file builds the one that is.

## Main results

- `instStarRing`, `instStarModule`: `FreeStarAlgebra X` is a ⋆-algebra over `ℂ` with
  `star (c • a) = conj c • star a`.
- `lift g`: every map `g : X → B` into a complex ⋆-algebra extends to a ⋆-homomorphism, with
  `lift_gen`.
- `hom_ext`: ⋆-homomorphisms out of `FreeStarAlgebra X` are determined on the generators.
- `adjoin_gen`: the generators and their adjoints generate `FreeStarAlgebra X` as an algebra.

## Reference

Blackadar, *Operator Algebras*, II.8.3.1.
-/

namespace GroupApproximation
namespace CStarLimits

noncomputable section

universe u v

/-- The free unital complex ⋆-algebra on `X`: `ℂ[FreeMonoid (X ⊕ X)]`, with the involution built
below. -/
abbrev FreeStarAlgebra (X : Type u) : Type u := MonoidAlgebra ℂ (FreeMonoid (X ⊕ X))

namespace FreeStarAlgebra

variable {X : Type u}

/-! ## The involution on words -/

/-- The involution on words: reverse the word and swap every letter with its adjoint. -/
def wordStar (w : FreeMonoid (X ⊕ X)) : FreeMonoid (X ⊕ X) :=
  FreeMonoid.reverse (FreeMonoid.map Sum.swap w)

@[simp] theorem wordStar_of (a : X ⊕ X) : wordStar (FreeMonoid.of a) = FreeMonoid.of a.swap :=
  rfl

theorem wordStar_one : wordStar (1 : FreeMonoid (X ⊕ X)) = 1 := rfl

theorem wordStar_mul (w v : FreeMonoid (X ⊕ X)) : wordStar (w * v) = wordStar v * wordStar w := by
  unfold wordStar
  rw [map_mul, FreeMonoid.reverse_mul]

theorem wordStar_wordStar (w : FreeMonoid (X ⊕ X)) : wordStar (wordStar w) = w := by
  induction w using FreeMonoid.inductionOn' with
  | one => rfl
  | mul_of a w ih =>
    rw [wordStar_mul, wordStar_mul, ih, wordStar_of, wordStar_of, Sum.swap_swap]

/-- The involution on words, as an equivalence. -/
def wordStarEquiv : FreeMonoid (X ⊕ X) ≃ FreeMonoid (X ⊕ X) :=
  ⟨wordStar, wordStar, wordStar_wordStar, wordStar_wordStar⟩

/-! ## The involution on the algebra -/

/-- The involution: `(Σ c_w w)^* = Σ conj(c_w) w^*`, defined coefficientwise. -/
instance instStar : Star (FreeStarAlgebra X) where
  star x := MonoidAlgebra.ofCoeff
    (Finsupp.mapRange star (star_zero ℂ) (x.coeff.equivMapDomain wordStarEquiv))

@[simp] theorem coeff_star (x : FreeStarAlgebra X) (w : FreeMonoid (X ⊕ X)) :
    (star x).coeff w = star (x.coeff (wordStar w)) := rfl

@[simp] theorem star_single (w : FreeMonoid (X ⊕ X)) (c : ℂ) :
    star (MonoidAlgebra.single w c : FreeStarAlgebra X) =
      MonoidAlgebra.single (wordStar w) (star c) := by
  ext h
  rw [coeff_star, MonoidAlgebra.coeff_single, MonoidAlgebra.coeff_single]
  by_cases hgh : wordStar w = h
  · rw [← hgh, wordStar_wordStar, Finsupp.single_eq_same, Finsupp.single_eq_same]
  · rw [Finsupp.single_eq_of_ne (fun hcon => hgh (by rw [← hcon, wordStar_wordStar])),
      Finsupp.single_eq_of_ne (Ne.symm hgh), star_zero]

theorem star_zero_aux : star (0 : FreeStarAlgebra X) = 0 := by
  ext g
  simp

theorem star_add_aux (x y : FreeStarAlgebra X) : star (x + y) = star x + star y := by
  ext g
  simp

theorem star_involutive_aux :
    Function.Involutive (star : FreeStarAlgebra X → FreeStarAlgebra X) := by
  intro x
  ext g
  simp [wordStar_wordStar]

theorem star_single_mul (w : FreeMonoid (X ⊕ X)) (c : ℂ) (y : FreeStarAlgebra X) :
    star (MonoidAlgebra.single w c * y) = star y * star (MonoidAlgebra.single w c) := by
  induction y using MonoidAlgebra.induction_linear with
  | zero => rw [mul_zero, star_zero_aux, zero_mul]
  | add a b ha hb => rw [mul_add, star_add_aux, ha, hb, star_add_aux, add_mul]
  | single v d =>
      rw [MonoidAlgebra.single_mul_single, star_single, star_single, star_single,
        MonoidAlgebra.single_mul_single, wordStar_mul, star_mul]

theorem star_mul_aux (x y : FreeStarAlgebra X) : star (x * y) = star y * star x := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => rw [zero_mul, star_zero_aux, mul_zero]
  | add a b ha hb => rw [add_mul, star_add_aux, ha, hb, star_add_aux, mul_add]
  | single w c => exact star_single_mul w c y

instance instStarRing : StarRing (FreeStarAlgebra X) where
  star_involutive := star_involutive_aux
  star_mul := star_mul_aux
  star_add := star_add_aux

instance instStarModule : StarModule ℂ (FreeStarAlgebra X) where
  star_smul r x := by
    ext g
    rw [coeff_star, MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.coeff_smul_apply,
      coeff_star, smul_eq_mul, smul_eq_mul, star_mul, mul_comm]

/-! ## Generators -/

/-- The generator `x` of the free ⋆-algebra. -/
def gen (x : X) : FreeStarAlgebra X := MonoidAlgebra.single (FreeMonoid.of (Sum.inl x)) 1

theorem star_gen (x : X) :
    star (gen x) = MonoidAlgebra.single (FreeMonoid.of (Sum.inr x)) (1 : ℂ) := by
  rw [gen, star_single, wordStar_of, Sum.swap_inl, star_one]

/-- A letter is a generator or the adjoint of one. -/
theorem single_letter_mem (a : X ⊕ X) :
    MonoidAlgebra.single (FreeMonoid.of a) (1 : ℂ) ∈
      Set.range (gen (X := X)) ∪ Set.range fun x : X ↦ star (gen x) := by
  rcases a with x | x
  · exact Set.mem_union_left _ ⟨x, rfl⟩
  · exact Set.mem_union_right _ ⟨x, star_gen x⟩

theorem single_of_mul (a : X ⊕ X) (w : FreeMonoid (X ⊕ X)) :
    (MonoidAlgebra.single (FreeMonoid.of a * w) (1 : ℂ) : FreeStarAlgebra X) =
      MonoidAlgebra.single (FreeMonoid.of a) 1 * MonoidAlgebra.single w 1 := by
  rw [MonoidAlgebra.single_mul_single, one_mul]

theorem single_eq_smul (w : FreeMonoid (X ⊕ X)) (c : ℂ) :
    (MonoidAlgebra.single w c : FreeStarAlgebra X) = c • MonoidAlgebra.single w 1 := by
  rw [MonoidAlgebra.smul_single', mul_one]

/-- **The generators and their adjoints generate the free ⋆-algebra.** -/
theorem adjoin_gen :
    Algebra.adjoin ℂ (Set.range (gen (X := X)) ∪ Set.range fun x : X ↦ star (gen x)) = ⊤ := by
  have hword : ∀ w : FreeMonoid (X ⊕ X), (MonoidAlgebra.single w (1 : ℂ) : FreeStarAlgebra X) ∈
      Algebra.adjoin ℂ (Set.range (gen (X := X)) ∪ Set.range fun x : X ↦ star (gen x)) := by
    intro w
    induction w using FreeMonoid.inductionOn' with
    | one => rw [← MonoidAlgebra.one_def]; exact one_mem _
    | mul_of a w ih =>
      rw [single_of_mul]
      exact mul_mem (Algebra.subset_adjoin (single_letter_mem a)) ih
  refine Algebra.eq_top_iff.mpr fun x ↦ ?_
  induction x using MonoidAlgebra.induction_linear with
  | zero => exact zero_mem _
  | add a b ha hb => exact add_mem ha hb
  | single w c =>
    rw [single_eq_smul]
    exact (Algebra.adjoin ℂ _).smul_mem (hword w) c

/-! ## The universal property -/

section Lift

variable {B : Type v} [Semiring B] [StarRing B]

/-- The monoid homomorphism on words determined by `g` on the generators. -/
def wordLift (g : X → B) : FreeMonoid (X ⊕ X) →* B :=
  FreeMonoid.lift (Sum.elim g fun x ↦ star (g x))

theorem wordLift_of_inl (g : X → B) (x : X) : wordLift g (FreeMonoid.of (Sum.inl x)) = g x :=
  rfl

theorem wordLift_of_inr (g : X → B) (x : X) :
    wordLift g (FreeMonoid.of (Sum.inr x)) = star (g x) :=
  rfl

theorem wordLift_star (g : X → B) (w : FreeMonoid (X ⊕ X)) :
    star (wordLift g w) = wordLift g (wordStar w) := by
  induction w using FreeMonoid.inductionOn' with
  | one => rw [wordStar_one, map_one, star_one]
  | mul_of a w ih =>
    rw [map_mul, star_mul, ih, wordStar_mul, map_mul, wordStar_of]
    rcases a with x | x
    · rw [Sum.swap_inl, wordLift_of_inl, wordLift_of_inr]
    · rw [Sum.swap_inr, wordLift_of_inl, wordLift_of_inr, star_star]

variable [Algebra ℂ B] [StarModule ℂ B]

theorem lift_map_star (g : X → B) (x : FreeStarAlgebra X) :
    MonoidAlgebra.lift ℂ B (FreeMonoid (X ⊕ X)) (wordLift g) (star x) =
      star (MonoidAlgebra.lift ℂ B (FreeMonoid (X ⊕ X)) (wordLift g) x) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => rw [star_zero_aux, map_zero, star_zero]
  | add a b ha hb => rw [star_add_aux, map_add, map_add, ha, hb, star_add]
  | single w c =>
      rw [star_single, MonoidAlgebra.lift_single, MonoidAlgebra.lift_single, star_smul,
        wordLift_star]

/-- **The universal property of the free ⋆-algebra.**  A map `g : X → B` into a complex
⋆-algebra extends to a ⋆-homomorphism. -/
def lift (g : X → B) : FreeStarAlgebra X →⋆ₐ[ℂ] B :=
  { MonoidAlgebra.lift ℂ B (FreeMonoid (X ⊕ X)) (wordLift g) with map_star' := lift_map_star g }

@[simp] theorem lift_gen (g : X → B) (x : X) : lift g (gen x) = g x := by
  show MonoidAlgebra.lift ℂ B (FreeMonoid (X ⊕ X)) (wordLift g)
      (MonoidAlgebra.single (FreeMonoid.of (Sum.inl x)) 1) = g x
  rw [MonoidAlgebra.lift_single, one_smul, wordLift_of_inl]

omit [StarModule ℂ B] in
/-- **⋆-homomorphisms out of the free ⋆-algebra are determined on the generators.** -/
theorem hom_ext {F₁ F₂ : FreeStarAlgebra X →⋆ₐ[ℂ] B} (h : ∀ x, F₁ (gen x) = F₂ (gen x)) :
    F₁ = F₂ := by
  have hletter : ∀ a : X ⊕ X, F₁ (MonoidAlgebra.single (FreeMonoid.of a) 1) =
      F₂ (MonoidAlgebra.single (FreeMonoid.of a) 1) := by
    rintro (x | x)
    · exact h x
    · rw [← star_gen, map_star, map_star, h x]
  have hword : ∀ w : FreeMonoid (X ⊕ X), F₁ (MonoidAlgebra.single w 1) =
      F₂ (MonoidAlgebra.single w 1) := by
    intro w
    induction w using FreeMonoid.inductionOn' with
    | one => rw [← MonoidAlgebra.one_def, map_one, map_one]
    | mul_of a w ih => rw [single_of_mul, map_mul, map_mul, hletter a, ih]
  refine StarAlgHom.ext fun x ↦ ?_
  induction x using MonoidAlgebra.induction_linear with
  | zero => rw [map_zero, map_zero]
  | add a b ha hb => rw [map_add, map_add, ha, hb]
  | single w c => rw [single_eq_smul, map_smul, map_smul, hword w]

/-- Existence and uniqueness of the extension of `g`. -/
theorem existsUnique_lift (g : X → B) :
    ∃! F : FreeStarAlgebra X →⋆ₐ[ℂ] B, ∀ x, F (gen x) = g x :=
  ⟨lift g, lift_gen g, fun F hF ↦ hom_ext fun x ↦ by rw [hF x, lift_gen]⟩

end Lift

end FreeStarAlgebra

end

end CStarLimits
end GroupApproximation
