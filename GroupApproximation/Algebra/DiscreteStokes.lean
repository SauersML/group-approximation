import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import GroupApproximation.Meta.AxiomGuard

/-!
# A discrete Stokes formula along free words

Let `Q` be a group, `f : α → Q` an assignment of values to letters, and
`φ ψ : Q → ℤ`.  Reading a free word `L` from a base point `b` traces a path in `Q`,
and along each edge `g → h` of that path we record the trapezoid term
`(φ g + φ h) * (ψ h - ψ g)`, a discrete `φ dψ`.  The sum is `wordSum f φ ψ b L`.

The edge term is antisymmetric, so the sum does not change under free reduction:
it descends to the free group (`freeSum`).  It is additive along products, and a
conjugate `c * s * c⁻¹` of a word `s` whose value in `Q` is trivial contributes
exactly the sum along `s`, based at the endpoint of `c`.  So an element written as
a product of `n` conjugates of closed words contributes at most `n` times the
largest sum along one of them.

For functions that move by at most one along every letter, the sum along a closed
word of length `ℓ` is at most `ℓ²` in absolute value (`abs_wordSum_le_of_closed`).
Choosing `φ`, `ψ` as truncated distance functions to parts of a loop turns the sum
into a lower bound for the loop's algebraic area without any planar diagram: this
is the quadrangle (Besicovitch) inequality used in Gromov's theorem that a linear
isoperimetric inequality over bounded relators makes a group hyperbolic.
-/

namespace GroupApproximation
namespace DiscreteStokes

universe u v

variable {α : Type u} {Q : Type v} [Group Q]

/-! ## Letters and words -/

/-- The value in `Q` of one free letter. -/
def letterVal (f : α → Q) (x : α × Bool) : Q :=
  cond x.2 (f x.1) (f x.1)⁻¹

@[simp] theorem letterVal_true (f : α → Q) (a : α) : letterVal f (a, true) = f a := rfl

@[simp] theorem letterVal_false (f : α → Q) (a : α) :
    letterVal f (a, false) = (f a)⁻¹ := rfl

/-- The formally inverse letter has the inverse value. -/
theorem letterVal_not (f : α → Q) (a : α) (bb : Bool) :
    letterVal f (a, !bb) = (letterVal f (a, bb))⁻¹ := by
  cases bb <;> simp

/-- The value in `Q` of a free word. -/
def wordVal (f : α → Q) (L : List (α × Bool)) : Q :=
  (L.map (letterVal f)).prod

@[simp] theorem wordVal_nil (f : α → Q) : wordVal f [] = 1 := rfl

theorem wordVal_cons (f : α → Q) (x : α × Bool) (L : List (α × Bool)) :
    wordVal f (x :: L) = letterVal f x * wordVal f L := by
  simp [wordVal]

theorem wordVal_append (f : α → Q) (L M : List (α × Bool)) :
    wordVal f (L ++ M) = wordVal f L * wordVal f M := by
  simp [wordVal, List.prod_append]

/-- The universal homomorphism evaluates a word letter by letter. -/
@[simp] theorem lift_mk_eq_wordVal (f : α → Q) (L : List (α × Bool)) :
    FreeGroup.lift f (FreeGroup.mk L) = wordVal f L := rfl

/-! ## The edge term and the sum along a word -/

/-- The trapezoid term of the discrete form `φ dψ` along the edge `g → h`. -/
def edgeTerm (φ ψ : Q → ℤ) (g h : Q) : ℤ :=
  (φ g + φ h) * (ψ h - ψ g)

omit [Group Q] in
/-- Reversing an edge negates its term. -/
theorem edgeTerm_swap (φ ψ : Q → ℤ) (g h : Q) :
    edgeTerm φ ψ h g = -edgeTerm φ ψ g h := by
  unfold edgeTerm
  ring

/-- **The discrete integral of `φ dψ`** along the path a word traces from `b`. -/
def wordSum (f : α → Q) (φ ψ : Q → ℤ) : Q → List (α × Bool) → ℤ
  | _, [] => 0
  | b, x :: L => edgeTerm φ ψ b (b * letterVal f x) + wordSum f φ ψ (b * letterVal f x) L

@[simp] theorem wordSum_nil (f : α → Q) (φ ψ : Q → ℤ) (b : Q) :
    wordSum f φ ψ b [] = 0 := rfl

@[simp] theorem wordSum_cons (f : α → Q) (φ ψ : Q → ℤ) (b : Q) (x : α × Bool)
    (L : List (α × Bool)) :
    wordSum f φ ψ b (x :: L) =
      edgeTerm φ ψ b (b * letterVal f x) + wordSum f φ ψ (b * letterVal f x) L := rfl

/-- The integral is additive along concatenation. -/
theorem wordSum_append (f : α → Q) (φ ψ : Q → ℤ) (b : Q) (L M : List (α × Bool)) :
    wordSum f φ ψ b (L ++ M) = wordSum f φ ψ b L + wordSum f φ ψ (b * wordVal f L) M := by
  induction L generalizing b with
  | nil => simp
  | cons x L ih =>
      rw [List.cons_append, wordSum_cons, wordSum_cons, ih, wordVal_cons, mul_assoc]
      ring

/-- A letter followed by its formal inverse contributes nothing. -/
theorem wordSum_cancel (f : α → Q) (φ ψ : Q → ℤ) (b : Q) (a : α) (bb : Bool)
    (L : List (α × Bool)) :
    wordSum f φ ψ b ((a, bb) :: (a, !bb) :: L) = wordSum f φ ψ b L := by
  rw [wordSum_cons, wordSum_cons, letterVal_not, mul_inv_cancel_right,
    edgeTerm_swap φ ψ b]
  ring

/-- **Invariance under one free reduction step.** -/
theorem wordSum_step (f : α → Q) (φ ψ : Q → ℤ) (b : Q) {L₁ L₂ : List (α × Bool)}
    (h : FreeGroup.Red.Step L₁ L₂) : wordSum f φ ψ b L₁ = wordSum f φ ψ b L₂ := by
  cases h with
  | @not L L' a bb =>
      rw [wordSum_append, wordSum_append, wordSum_cancel]

/-! ## The sum on the free group -/

/-- **The discrete integral on the free group.** -/
def freeSum (f : α → Q) (φ ψ : Q → ℤ) (b : Q) : FreeGroup α → ℤ :=
  Quot.lift (wordSum f φ ψ b) fun _ _ h => wordSum_step f φ ψ b h

@[simp] theorem freeSum_mk (f : α → Q) (φ ψ : Q → ℤ) (b : Q) (L : List (α × Bool)) :
    freeSum f φ ψ b (FreeGroup.mk L) = wordSum f φ ψ b L := rfl

@[simp] theorem freeSum_one (f : α → Q) (φ ψ : Q → ℤ) (b : Q) :
    freeSum f φ ψ b 1 = 0 := rfl

/-- The integral is additive along products, the second factor being read from
the endpoint of the first. -/
theorem freeSum_mul (f : α → Q) (φ ψ : Q → ℤ) (b : Q) (g h : FreeGroup α) :
    freeSum f φ ψ b (g * h) =
      freeSum f φ ψ b g + freeSum f φ ψ (b * FreeGroup.lift f g) h := by
  induction g using Quot.ind with
  | mk L =>
      induction h using Quot.ind with
      | mk M => exact wordSum_append f φ ψ b L M

/-- The inverse is read backwards from the endpoint. -/
theorem freeSum_inv (f : α → Q) (φ ψ : Q → ℤ) (b : Q) (g : FreeGroup α) :
    freeSum f φ ψ b g⁻¹ = -freeSum f φ ψ (b * (FreeGroup.lift f g)⁻¹) g := by
  have h := freeSum_mul f φ ψ b g⁻¹ g
  rw [inv_mul_cancel, freeSum_one, map_inv] at h
  linarith

/-- **A conjugate of a closed word contributes the sum along the word**, read from
the endpoint of the conjugator. -/
theorem freeSum_conj (f : α → Q) (φ ψ : Q → ℤ) (b : Q) (c s : FreeGroup α)
    (hs : FreeGroup.lift f s = 1) :
    freeSum f φ ψ b (c * s * c⁻¹) = freeSum f φ ψ (b * FreeGroup.lift f c) s := by
  rw [freeSum_mul, freeSum_mul, freeSum_inv, map_mul, hs, mul_one, mul_inv_cancel_right]
  ring

/-! ## The bound along a closed word -/

/-- `φ` moves by at most one along every letter of `L`, from every point. -/
def LipschitzAlong (f : α → Q) (φ : Q → ℤ) (L : List (α × Bool)) : Prop :=
  ∀ x ∈ L, ∀ g : Q, |φ (g * letterVal f x) - φ g| ≤ 1

/-- `φ` moves by at most one along every free letter. -/
def LipschitzOnLetters (f : α → Q) (φ : Q → ℤ) : Prop :=
  ∀ (g : Q) (x : α × Bool), |φ (g * letterVal f x) - φ g| ≤ 1

theorem LipschitzOnLetters.along {f : α → Q} {φ : Q → ℤ} (h : LipschitzOnLetters f φ)
    (L : List (α × Bool)) : LipschitzAlong f φ L :=
  fun x _ g => h g x

theorem LipschitzAlong.tail {f : α → Q} {φ : Q → ℤ} {x : α × Bool} {L : List (α × Bool)}
    (h : LipschitzAlong f φ (x :: L)) : LipschitzAlong f φ L :=
  fun y hy g => h y (List.mem_cons_of_mem _ hy) g

theorem LipschitzAlong.head {f : α → Q} {φ : Q → ℤ} {x : α × Bool} {L : List (α × Bool)}
    (h : LipschitzAlong f φ (x :: L)) (g : Q) : |φ (g * letterVal f x) - φ g| ≤ 1 :=
  h x (by simp) g

/-- A function that moves by at most one per letter moves by at most the length
along a word. -/
theorem abs_endpoint_sub_le (f : α → Q) {ψ : Q → ℤ} :
    ∀ (L : List (α × Bool)), LipschitzAlong f ψ L → ∀ b : Q,
      |ψ (b * wordVal f L) - ψ b| ≤ L.length
  | [], _, b => by simp
  | x :: L, hψ, b => by
      have h1 := abs_le.mp (hψ.head b)
      have h2 := abs_le.mp (abs_endpoint_sub_le f L hψ.tail (b * letterVal f x))
      rw [wordVal_cons, ← mul_assoc, List.length_cons]
      push_cast
      rw [abs_le]
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- **The sum along a word, up to its boundary term, is at most the square of the
length.**  The boundary term `2 φ(b) (ψ(end) - ψ(b))` is what shifting `φ` by the
constant `φ b` changes; for a closed word it vanishes. -/
theorem abs_wordSum_sub_le (f : α → Q) {φ ψ : Q → ℤ} :
    ∀ (L : List (α × Bool)), LipschitzAlong f φ L → LipschitzAlong f ψ L → ∀ b : Q,
      |wordSum f φ ψ b L - 2 * φ b * (ψ (b * wordVal f L) - ψ b)| ≤ (L.length : ℤ) ^ 2
  | [], _, _, b => by simp
  | x :: L, hφ, hψ, b => by
      have hIH := abs_le.mp (abs_wordSum_sub_le f L hφ.tail hψ.tail (b * letterVal f x))
      have hprod1 : |(φ (b * letterVal f x) - φ b) * (ψ (b * letterVal f x) - ψ b)| ≤ 1 := by
        rw [abs_mul]
        calc |φ (b * letterVal f x) - φ b| * |ψ (b * letterVal f x) - ψ b| ≤ 1 * 1 :=
              mul_le_mul (hφ.head b) (hψ.head b) (abs_nonneg _) zero_le_one
          _ = 1 := one_mul 1
      have hprod2 : |(φ (b * letterVal f x) - φ b) *
          (ψ (b * letterVal f x * wordVal f L) - ψ (b * letterVal f x))| ≤ L.length := by
        rw [abs_mul]
        calc |φ (b * letterVal f x) - φ b| *
              |ψ (b * letterVal f x * wordVal f L) - ψ (b * letterVal f x)|
            ≤ 1 * (L.length : ℤ) :=
              mul_le_mul (hφ.head b) (abs_endpoint_sub_le f L hψ.tail (b * letterVal f x))
                (abs_nonneg _) zero_le_one
          _ = L.length := one_mul _
      have h1 := abs_le.mp hprod1
      have h2 := abs_le.mp hprod2
      have key : wordSum f φ ψ b (x :: L) -
            2 * φ b * (ψ (b * wordVal f (x :: L)) - ψ b) =
          (wordSum f φ ψ (b * letterVal f x) L -
              2 * φ (b * letterVal f x) *
                (ψ (b * letterVal f x * wordVal f L) - ψ (b * letterVal f x))) +
            (φ (b * letterVal f x) - φ b) * (ψ (b * letterVal f x) - ψ b) +
            2 * ((φ (b * letterVal f x) - φ b) *
              (ψ (b * letterVal f x * wordVal f L) - ψ (b * letterVal f x))) := by
        rw [wordSum_cons, wordVal_cons, ← mul_assoc]
        unfold edgeTerm
        ring
      rw [key, List.length_cons, abs_le]
      push_cast
      have hsq : ((L.length : ℤ) + 1) ^ 2 = (L.length : ℤ) ^ 2 + 2 * L.length + 1 := by ring
      rw [hsq]
      constructor <;> linarith [hIH.1, hIH.2, h1.1, h1.2, h2.1, h2.2]

/-- **Along a closed word of length `ℓ` the sum is at most `ℓ²`.** -/
theorem abs_wordSum_le_of_closed (f : α → Q) {φ ψ : Q → ℤ} (L : List (α × Bool))
    (hφ : LipschitzAlong f φ L) (hψ : LipschitzAlong f ψ L) (b : Q)
    (hL : wordVal f L = 1) :
    |wordSum f φ ψ b L| ≤ (L.length : ℤ) ^ 2 := by
  have h := abs_wordSum_sub_le f L hφ hψ b
  rwa [hL, mul_one, sub_self, mul_zero, sub_zero] at h

/-- **A closed free element contributes at most the square of its length.** -/
theorem abs_freeSum_le_of_lift_eq_one [DecidableEq α] (f : α → Q) {φ ψ : Q → ℤ}
    (hφ : LipschitzOnLetters f φ) (hψ : LipschitzOnLetters f ψ) (b : Q)
    (s : FreeGroup α) (hs : FreeGroup.lift f s = 1) :
    |freeSum f φ ψ b s| ≤ (FreeGroup.norm s : ℤ) ^ 2 := by
  have hmk : FreeGroup.mk s.toWord = s := FreeGroup.mk_toWord
  have hclosed : wordVal f s.toWord = 1 := by
    rw [← lift_mk_eq_wordVal, hmk, hs]
  have h := abs_wordSum_le_of_closed f s.toWord (hφ.along _) (hψ.along _) b hclosed
  calc |freeSum f φ ψ b s| = |wordSum f φ ψ b s.toWord| := by
        rw [← freeSum_mk, hmk]
    _ ≤ (s.toWord.length : ℤ) ^ 2 := h
    _ = (FreeGroup.norm s : ℤ) ^ 2 := rfl

end DiscreteStokes
end GroupApproximation

#audit_axioms GroupApproximation.DiscreteStokes.wordSum_step
#audit_axioms GroupApproximation.DiscreteStokes.freeSum_mul
#audit_axioms GroupApproximation.DiscreteStokes.freeSum_conj
#audit_axioms GroupApproximation.DiscreteStokes.abs_wordSum_sub_le
#audit_axioms GroupApproximation.DiscreteStokes.abs_freeSum_le_of_lift_eq_one
