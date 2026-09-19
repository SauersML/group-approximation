import GroupApproximation.Analysis.RatComplexSubfield
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Tactic.DeriveCountable

/-!
# Countable rational noncommutative star polynomials

The reduced-product diagonal argument uses only the countability of the
noncommutative star polynomials over `Q(i)`, their evaluation, and the fact
that evaluation commutes with a possibly nonunital star homomorphism.  A
nonunital syntax is essential: `HasMFEmbedding` deliberately permits
nonunital embeddings, so constants other than zero would not be functorial.

The scalar coefficients are pairs of rationals, interpreted as rational
complex numbers.  `generatorBound p` is one more than every generator index
appearing in `p`; it records the manuscript condition that the first `n`
polynomials involve only the first `n` generators.
-/

namespace GroupApproximation
namespace RationalNoncommutativeStarPolynomial

open RatComplexSubfield RationalHermitian

/-- Formal nonunital noncommutative star polynomials over the rational complex
numbers, on countably many generators. -/
inductive Polynomial where
  | zero : Polynomial
  | generator : ℕ → Polynomial
  | smul : (ℚ × ℚ) → Polynomial → Polynomial
  | add : Polynomial → Polynomial → Polynomial
  | mul : Polynomial → Polynomial → Polynomial
  | star : Polynomial → Polynomial
  deriving DecidableEq, Countable

instance : Inhabited Polynomial := ⟨.zero⟩

/-- One more than every generator index occurring in a polynomial. -/
def generatorBound : Polynomial → ℕ
  | .zero => 0
  | .generator i => i + 1
  | .smul _ p => generatorBound p
  | .add p q => max (generatorBound p) (generatorBound q)
  | .mul p q => max (generatorBound p) (generatorBound q)
  | .star p => generatorBound p

/-- Formal additive inverse, using the rational scalar `-1`. -/
def neg (p : Polynomial) : Polynomial := .smul (-1, 0) p

/-- Formal subtraction. -/
def sub (p q : Polynomial) : Polynomial := .add p (neg q)

/-- Evaluation in a complex star algebra at a countable family. -/
def eval {A : Type*} [NonUnitalCStarAlgebra A] (a : ℕ → A) :
    Polynomial → A
  | .zero => 0
  | .generator i => a i
  | .smul q p => ofRatPair q • eval a p
  | .add p q => eval a p + eval a q
  | .mul p q => eval a p * eval a q
  | .star p => star (eval a p)

@[simp] theorem eval_zero {A : Type*} [NonUnitalCStarAlgebra A]
    (a : ℕ → A) : eval a .zero = 0 := rfl

@[simp] theorem eval_generator {A : Type*} [NonUnitalCStarAlgebra A]
    (a : ℕ → A) (i : ℕ) : eval a (.generator i) = a i := rfl

@[simp] theorem eval_smul {A : Type*} [NonUnitalCStarAlgebra A]
    (a : ℕ → A) (q : ℚ × ℚ) (p : Polynomial) :
    eval a (.smul q p) = ofRatPair q • eval a p := rfl

@[simp] theorem eval_add {A : Type*} [NonUnitalCStarAlgebra A]
    (a : ℕ → A) (p q : Polynomial) :
    eval a (.add p q) = eval a p + eval a q := rfl

@[simp] theorem eval_mul {A : Type*} [NonUnitalCStarAlgebra A]
    (a : ℕ → A) (p q : Polynomial) :
    eval a (.mul p q) = eval a p * eval a q := rfl

@[simp] theorem eval_star {A : Type*} [NonUnitalCStarAlgebra A]
    (a : ℕ → A) (p : Polynomial) :
    eval a (.star p) = star (eval a p) := rfl

@[simp] theorem eval_neg {A : Type*} [NonUnitalCStarAlgebra A]
    (a : ℕ → A) (p : Polynomial) : eval a (neg p) = -eval a p := by
  change RationalHermitian.ofRatPair (-1, 0) • eval a p = -eval a p
  have hscalar : RationalHermitian.ofRatPair (-1, 0) = (-1 : ℂ) := by
    apply Complex.ext <;> simp [RationalHermitian.ofRatPair]
  rw [hscalar, neg_one_smul]

@[simp] theorem eval_sub {A : Type*} [NonUnitalCStarAlgebra A]
    (a : ℕ → A) (p q : Polynomial) :
    eval a (sub p q) = eval a p - eval a q := by
  rw [sub, eval_add, eval_neg, sub_eq_add_neg]

/-- Evaluation is functorial for nonunital star homomorphisms. -/
theorem map_eval {A B : Type*} [NonUnitalCStarAlgebra A]
    [NonUnitalCStarAlgebra B] (f : A →⋆ₙₐ[ℂ] B) (a : ℕ → A)
    (p : Polynomial) : f (eval a p) = eval (fun i ↦ f (a i)) p := by
  induction p with
  | zero => exact map_zero f
  | generator i => rfl
  | smul q p hp => rw [eval_smul, map_smul, hp, eval_smul]
  | add p q hp hq => rw [eval_add, map_add, hp, hq, eval_add]
  | mul p q hp hq => rw [eval_mul, map_mul, hp, hq, eval_mul]
  | star p hp => rw [eval_star, map_star, hp, eval_star]

/-- A raw surjective enumeration, supplied by countability. -/
noncomputable def rawEnumeration : ℕ → Polynomial :=
  Classical.choose (exists_surjective_nat Polynomial)

theorem rawEnumeration_surjective : Function.Surjective rawEnumeration :=
  Classical.choose_spec (exists_surjective_nat Polynomial)

/-- The manuscript enumeration, with the zero polynomial first. -/
noncomputable def enumeration : ℕ → Polynomial
  | 0 => .zero
  | n + 1 => rawEnumeration n

@[simp] theorem enumeration_zero : enumeration 0 = .zero := rfl

/-- Prefixing a surjective enumeration by zero preserves surjectivity. -/
theorem enumeration_surjective : Function.Surjective enumeration := by
  intro p
  obtain ⟨n, hn⟩ := rawEnumeration_surjective p
  exact ⟨n + 1, hn⟩

/-- The manuscript's finite family `P_n`: the first `n` enumerated
polynomials which use only the first `n` generators. -/
noncomputable def finiteFamily (n : ℕ) : Finset Polynomial :=
  (Finset.range n).image enumeration |>.filter fun p ↦ generatorBound p ≤ n

theorem mem_finiteFamily_iff {n : ℕ} {p : Polynomial} :
    p ∈ finiteFamily n ↔
      (∃ j < n, enumeration j = p) ∧ generatorBound p ≤ n := by
  simp [finiteFamily]

/-- `P_n` is nonempty for every positive stage because zero is enumerated
first and uses no generators. -/
theorem zero_mem_finiteFamily {n : ℕ} (hn : 0 < n) :
    .zero ∈ finiteFamily n := by
  rw [mem_finiteFamily_iff]
  exact ⟨⟨0, hn, enumeration_zero⟩, Nat.zero_le n⟩

/-- Every polynomial eventually appears in the manuscript's finite families:
after its enumeration index and generator bound. -/
theorem eventually_mem_prefix_and_generatorBound (p : Polynomial) :
    ∃ N, ∃ j < N, enumeration j = p ∧ generatorBound p ≤ N := by
  obtain ⟨j, hj⟩ := enumeration_surjective p
  refine ⟨max (j + 1) (generatorBound p), j, ?_, hj, ?_⟩
  · exact lt_of_lt_of_le (Nat.lt_succ_self j) (Nat.le_max_left _ _)
  · exact Nat.le_max_right _ _

/-- Every fixed polynomial belongs to every sufficiently late finite family,
not merely to one of them. -/
theorem eventually_mem_finiteFamily (p : Polynomial) :
    ∀ᶠ n in Filter.atTop, p ∈ finiteFamily n := by
  obtain ⟨N, j, hjN, hjp, hpN⟩ :=
    eventually_mem_prefix_and_generatorBound p
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  rw [mem_finiteFamily_iff]
  exact ⟨⟨j, hjN.trans_le hn, hjp⟩, hpN.trans hn⟩

end RationalNoncommutativeStarPolynomial
end GroupApproximation
