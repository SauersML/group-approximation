import GroupApproximation.Leavitt.MatrixSelfSimilarity
import Mathlib.Data.List.Infix
import Mathlib.Tactic.NoncommRing
import GroupApproximation.Meta.AxiomGuard

/-!
# Leaf calculus at arbitrary arity

`Leavitt/LeavittWords.lean` develops the word calculus — `s_α`, `t_α`, the
orthogonality relations, and the cylinder projections `p_α = s_α t_α` — over a
`LeavittFamily A`.  That structure is **binary by construction**: four fields
`s0 s1 t0 t1` and words in `List (Fin 2)`.  Its file is general over the *ring*
and not over the *arity*, so none of it applies to `L_k(1,d)` for `d ≥ 3`.

This module is the same calculus over a `CompleteMatrixFamily A ι`, whose two
fields are exactly the relations the binary development actually uses:

* `orthogonal : right i * left j = if i = j then 1 else 0` — the binary
  `t_mul_s`;
* `complete : ∑ i, left i * right i = 1` — the binary `sum_s_mul_t`.

Nothing else about the family is consumed anywhere in the binary file, which is
why the generalisation is a substitution rather than a reproof.  The only clauses
that change shape are the splittings: where the binary file writes a two-term sum
`s₀t₀ + s₁t₁`, this one writes `∑ i : ι`.

## Why this module exists on its own

It is the first stage of generalising the chain
`LeavittWords → LeavittNormalForm → LeavittSimplicity → division` from arity `2`
to arity `d`, which is what `HasSingleSandwichDivision (AryLeavittAlgebra k d)`
needs.  Doing the words layer first is a measurement: if it generalises cleanly
the remaining modules are a mechanical follow-through, and if it does not the
obstruction is found here rather than three modules later.

## A knowing overlap

`not_prefix_append_left` and `not_prefix_append_right` below are stated for
`List α`.  `LeavittFamily.not_prefix_append_left`/`_right` are the `Fin 2`
instances of the same two facts, with no ring content at all; they were stated at
`List (Fin 2)` because that file had no reason to be general.  These are the
versions to keep.  The binary copies are left untouched rather than swept —
whoever is next in `LeavittWords.lean` for its own reasons can point them here.
-/

namespace GroupApproximation
namespace CompleteMatrixFamily

/-! ### List facts, with no ring content -/

section ListFacts

variable {α : Type*}

/-- Words with a common prefix stay incomparable when the prefix is removed. -/
theorem not_prefix_append_left (l a b : List α) (hab : ¬a <+: b) :
    ¬ l ++ a <+: l ++ b := by
  intro h
  exact hab (by simpa using h)

/-- Incomparable words remain incomparable after arbitrary extension. -/
theorem not_prefix_append_right (a b x y : List α)
    (hab : ¬a <+: b) (hba : ¬b <+: a) : ¬ a ++ x <+: b ++ y := by
  intro h
  have ha : a <+: b ++ y := (List.prefix_append a x).trans h
  by_cases hle : a.length ≤ b.length
  · exact hab ((List.isPrefix_append_of_length hle).mp ha)
  · apply hba
    rw [List.prefix_iff_eq_take]
    have hea := List.prefix_iff_eq_take.mp ha
    rw [hea, List.take_take, Nat.min_eq_left (Nat.le_of_not_ge hle)]
    simp

end ListFacts

/-! ### The word calculus -/

variable {A : Type*} [Ring A] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (F : CompleteMatrixFamily A ι)

/-- `s_α` for a finite word `α` over the index type. -/
def wordS : List ι → A
  | [] => 1
  | i :: a => F.left i * wordS a

/-- `t_α` for a finite word `α` over the index type. -/
def wordT : List ι → A
  | [] => 1
  | i :: a => wordT a * F.right i

@[simp] theorem wordS_nil : F.wordS [] = 1 := rfl
@[simp] theorem wordT_nil : F.wordT [] = 1 := rfl

@[simp] theorem wordS_cons (i : ι) (a : List ι) :
    F.wordS (i :: a) = F.left i * F.wordS a := rfl

@[simp] theorem wordT_cons (i : ι) (a : List ι) :
    F.wordT (i :: a) = F.wordT a * F.right i := rfl

theorem wordS_append (a b : List ι) :
    F.wordS (a ++ b) = F.wordS a * F.wordS b := by
  induction a with
  | nil => simp
  | cons i a ih => simp [ih, mul_assoc]

theorem wordT_append (a b : List ι) :
    F.wordT (a ++ b) = F.wordT b * F.wordT a := by
  induction a with
  | nil => simp
  | cons i a ih => simp [ih, mul_assoc]

@[simp] theorem wordS_singleton (i : ι) : F.wordS [i] = F.left i := by
  simp

@[simp] theorem wordT_singleton (i : ι) : F.wordT [i] = F.right i := by
  simp

/-- **Leaf calculus (i)**: `t_α s_α = 1`. -/
theorem wordT_mul_wordS_self (a : List ι) : F.wordT a * F.wordS a = 1 := by
  induction a with
  | nil => simp
  | cons i a ih =>
      calc F.wordT (i :: a) * F.wordS (i :: a)
          = F.wordT a * ((F.right i * F.left i) * F.wordS a) := by
            simp only [wordT_cons, wordS_cons, mul_assoc]
        _ = 1 := by simp [F.orthogonal, ih]

/-- **Leaf calculus (ii)**: `t_α s_β = 0` for incomparable words. -/
theorem wordT_mul_wordS_of_incomparable (a b : List ι)
    (hab : ¬a <+: b) (hba : ¬b <+: a) : F.wordT a * F.wordS b = 0 := by
  induction a generalizing b with
  | nil => exact (hab (by simp)).elim
  | cons i a ih =>
      cases b with
      | nil => exact (hba (by simp)).elim
      | cons j b =>
          by_cases hij : i = j
          · subst hij
            have hab' : ¬a <+: b := fun hp => hab (by simpa using hp)
            have hba' : ¬b <+: a := fun hp => hba (by simpa using hp)
            calc F.wordT (i :: a) * F.wordS (i :: b)
                = F.wordT a * ((F.right i * F.left i) * F.wordS b) := by
                  simp only [wordT_cons, wordS_cons, mul_assoc]
              _ = F.wordT a * F.wordS b := by simp [F.orthogonal]
              _ = 0 := ih b hab' hba'
          · calc F.wordT (i :: a) * F.wordS (j :: b)
                = F.wordT a * ((F.right i * F.left j) * F.wordS b) := by
                  simp only [wordT_cons, wordS_cons, mul_assoc]
              _ = 0 := by simp [F.orthogonal, hij]

/-- Collapse of a left prefix: `t_α · s_{αγ} = s_γ`. -/
theorem wordT_mul_wordS_append_left (a e : List ι) :
    F.wordT a * F.wordS (a ++ e) = F.wordS e := by
  rw [wordS_append, ← mul_assoc, wordT_mul_wordS_self, one_mul]

/-- Collapse of a right prefix: `t_{αγ} · s_α = t_γ`. -/
theorem wordT_append_mul_wordS (a f : List ι) :
    F.wordT (a ++ f) * F.wordS a = F.wordT f := by
  rw [wordT_append, mul_assoc, wordT_mul_wordS_self, mul_one]

/-! ### Cylinders -/

/-- The cylinder projection `p_α = s_α t_α`. -/
def cylinder (a : List ι) : A := F.wordS a * F.wordT a

theorem cylinder_isIdempotent (a : List ι) :
    F.cylinder a * F.cylinder a = F.cylinder a := by
  unfold cylinder
  calc (F.wordS a * F.wordT a) * (F.wordS a * F.wordT a)
      = F.wordS a * (F.wordT a * F.wordS a) * F.wordT a := by noncomm_ring
    _ = F.wordS a * F.wordT a := by rw [wordT_mul_wordS_self]; simp

theorem cylinder_mul_of_incomparable (a b : List ι)
    (hab : ¬a <+: b) (hba : ¬b <+: a) : F.cylinder a * F.cylinder b = 0 := by
  unfold cylinder
  calc (F.wordS a * F.wordT a) * (F.wordS b * F.wordT b)
      = F.wordS a * (F.wordT a * F.wordS b) * F.wordT b := by noncomm_ring
    _ = 0 := by rw [wordT_mul_wordS_of_incomparable F a b hab hba]; simp

/-! ### The splittings

Where the binary file writes the two-term sum `s₀t₀ + s₁t₁`, these write
`∑ i : ι`.  This is the only place the arity is visible. -/

/-- **Leaf calculus (iii)**: a cylinder splits along all of its children. -/
theorem cylinder_split (a : List ι) :
    F.cylinder a = ∑ i : ι, F.cylinder (a ++ [i]) := by
  have hone : F.wordS a * F.wordT a
      = F.wordS a * (∑ i : ι, F.left i * F.right i) * F.wordT a := by
    rw [F.complete, mul_one]
  calc F.cylinder a = F.wordS a * (∑ i : ι, F.left i * F.right i) * F.wordT a :=
        hone
    _ = ∑ i : ι, F.wordS a * (F.left i * F.right i) * F.wordT a := by
        rw [Finset.mul_sum, Finset.sum_mul]
    _ = ∑ i : ι, F.cylinder (a ++ [i]) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [cylinder, wordS_append, wordT_append, wordS_singleton,
          wordT_singleton]
        noncomm_ring

/-- The simultaneous splitting of a prefix matrix coefficient. -/
theorem wordS_mul_wordT_split (a b : List ι) :
    F.wordS a * F.wordT b
      = ∑ i : ι, F.wordS (a ++ [i]) * F.wordT (b ++ [i]) := by
  have hone : F.wordS a * F.wordT b
      = F.wordS a * (∑ i : ι, F.left i * F.right i) * F.wordT b := by
    rw [F.complete, mul_one]
  calc F.wordS a * F.wordT b
      = F.wordS a * (∑ i : ι, F.left i * F.right i) * F.wordT b := hone
    _ = ∑ i : ι, F.wordS a * (F.left i * F.right i) * F.wordT b := by
        rw [Finset.mul_sum, Finset.sum_mul]
    _ = ∑ i : ι, F.wordS (a ++ [i]) * F.wordT (b ++ [i]) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [wordS_append, wordT_append, wordS_singleton, wordT_singleton]
        noncomm_ring

/-- The splitting of the prefixing operator. -/
theorem wordS_split (a : List ι) :
    F.wordS a = ∑ i : ι, F.wordS (a ++ [i]) * F.right i := by
  have hone : F.wordS a = F.wordS a * (∑ i : ι, F.left i * F.right i) := by
    rw [F.complete, mul_one]
  calc F.wordS a = F.wordS a * (∑ i : ι, F.left i * F.right i) := hone
    _ = ∑ i : ι, F.wordS a * (F.left i * F.right i) := by rw [Finset.mul_sum]
    _ = ∑ i : ι, F.wordS (a ++ [i]) * F.right i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [wordS_append, wordS_singleton]
        noncomm_ring

/-- The splitting of the deletion operator. -/
theorem wordT_split (a : List ι) :
    F.wordT a = ∑ i : ι, F.left i * F.wordT (a ++ [i]) := by
  have hone : F.wordT a = (∑ i : ι, F.left i * F.right i) * F.wordT a := by
    rw [F.complete, one_mul]
  calc F.wordT a = (∑ i : ι, F.left i * F.right i) * F.wordT a := hone
    _ = ∑ i : ι, (F.left i * F.right i) * F.wordT a := by rw [Finset.sum_mul]
    _ = ∑ i : ι, F.left i * F.wordT (a ++ [i]) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [wordT_append, wordT_singleton]
        noncomm_ring

end CompleteMatrixFamily
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.CompleteMatrixFamily.wordT_mul_wordS_self
#audit_axioms GroupApproximation.CompleteMatrixFamily.wordT_mul_wordS_of_incomparable
#audit_axioms GroupApproximation.CompleteMatrixFamily.cylinder_isIdempotent
#audit_axioms GroupApproximation.CompleteMatrixFamily.cylinder_mul_of_incomparable
#audit_axioms GroupApproximation.CompleteMatrixFamily.cylinder_split
#audit_axioms GroupApproximation.CompleteMatrixFamily.wordS_mul_wordT_split
#audit_axioms GroupApproximation.CompleteMatrixFamily.wordS_split
#audit_axioms GroupApproximation.CompleteMatrixFamily.wordT_split
#audit_axioms GroupApproximation.CompleteMatrixFamily.not_prefix_append_right
