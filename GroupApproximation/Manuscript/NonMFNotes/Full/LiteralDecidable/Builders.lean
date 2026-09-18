import GroupApproximation.Manuscript.NonMFNotes.Full.LiteralDecidable.Poly
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Pairing

/-!
# Polynomial builders and matrix blocks (lane NN02c)

Manuscript: `thm:mf-radical-arithmetic` (non_mf_group_notes.tex), sentence
"This is decidable over the real closed field" (Tarski 1951, Seidenberg 1954).

Elementary complex polynomials used to write the defining conditions of the literal
predicate `NN02b.LiteralD` as a polynomial system, and the dictionary between unknowns
indexed by `Nat.pair` codes and `d × d` matrix blocks: the block `(b, e)` has entries
`ζ (cv b e j k)`.
-/

namespace GroupApproximation.Full.NN02c

open Matrix

noncomputable section

theorem evalC_append (ζ : ℕ → ℂ) (p q : CPoly) : evalC ζ (p ++ q) = evalC ζ p + evalC ζ q := by
  induction p with
  | nil =>
    show evalC ζ q = 0 + evalC ζ q
    rw [zero_add]
  | cons m p ih =>
    show (coefVal m.1 : ℂ) * monoC ζ m.2 + evalC ζ (p ++ q) =
      ((coefVal m.1 : ℂ) * monoC ζ m.2 + evalC ζ p) + evalC ζ q
    rw [ih, add_assoc]

/-- Negation of a complex polynomial. -/
def negC (p : CPoly) : CPoly := p.map fun m => (negCoef m.1, m.2)

theorem evalC_negC (ζ : ℕ → ℂ) (p : CPoly) : evalC ζ (negC p) = -evalC ζ p := by
  induction p with
  | nil =>
    show (0 : ℂ) = -0
    rw [neg_zero]
  | cons m p ih =>
    show (coefVal (negCoef m.1) : ℂ) * monoC ζ m.2 + evalC ζ (negC p) =
      -((coefVal m.1 : ℂ) * monoC ζ m.2 + evalC ζ p)
    rw [ih, coefVal_negCoef, Complex.ofReal_neg]
    ring

/-- Difference of two complex polynomials. -/
def diffC (p q : CPoly) : CPoly := p ++ negC q

theorem evalC_diffC (ζ : ℕ → ℂ) (p q : CPoly) :
    evalC ζ (diffC p q) = evalC ζ p - evalC ζ q := by
  show evalC ζ (p ++ negC q) = evalC ζ p - evalC ζ q
  rw [evalC_append, evalC_negC, sub_eq_add_neg]

/-- The monomial `n * a` for a single letter `a`. -/
def scaledVarC (n : ℕ) (a : ℕ × Bool) : CPoly := [((false, n), [a])]

theorem evalC_scaledVarC (ζ : ℕ → ℂ) (n : ℕ) (a : ℕ × Bool) :
    evalC ζ (scaledVarC n a) = (n : ℂ) * litC ζ a := by
  show (coefVal (false, n) : ℂ) * (litC ζ a * 1) + 0 = (n : ℂ) * litC ζ a
  rw [coefVal_false, Complex.ofReal_natCast, mul_one, add_zero]

/-- The single letter `a`. -/
def varC (a : ℕ × Bool) : CPoly := scaledVarC 1 a

theorem evalC_varC (ζ : ℕ → ℂ) (a : ℕ × Bool) : evalC ζ (varC a) = litC ζ a := by
  show evalC ζ (scaledVarC 1 a) = litC ζ a
  rw [evalC_scaledVarC, Nat.cast_one, one_mul]

/-- The constant `n`. -/
def constC (n : ℕ) : CPoly := [((false, n), [])]

theorem evalC_constC (ζ : ℕ → ℂ) (n : ℕ) : evalC ζ (constC n) = (n : ℂ) := by
  show (coefVal (false, n) : ℂ) * 1 + 0 = (n : ℂ)
  rw [coefVal_false, Complex.ofReal_natCast, mul_one, add_zero]

/-- The sum `∑_{l < d} n * f l * g l` of products of two letters. -/
def sumProd (n d : ℕ) (f g : ℕ → ℕ × Bool) : CPoly :=
  (List.range d).map fun l => ((false, n), [f l, g l])

theorem evalC_sumProd (ζ : ℕ → ℂ) (n d : ℕ) (f g : ℕ → ℕ × Bool) :
    evalC ζ (sumProd n d f g) =
      (n : ℂ) * ∑ l ∈ Finset.range d, litC ζ (f l) * litC ζ (g l) := by
  induction d with
  | zero =>
    show (0 : ℂ) = (n : ℂ) * ∑ l ∈ Finset.range 0, litC ζ (f l) * litC ζ (g l)
    rw [Finset.sum_range_zero, mul_zero]
  | succ d ih =>
    have hs : sumProd n (d + 1) f g = sumProd n d f g ++ [((false, n), [f d, g d])] := by
      show (List.range (d + 1)).map (fun l => ((false, n), [f l, g l])) =
        (List.range d).map (fun l => ((false, n), [f l, g l])) ++ [((false, n), [f d, g d])]
      rw [List.range_succ, List.map_append, List.map_singleton]
    rw [hs, evalC_append, ih, Finset.sum_range_succ, mul_add]
    show _ + ((coefVal (false, n) : ℂ) * (litC ζ (f d) * (litC ζ (g d) * 1)) + 0) = _
    rw [coefVal_false, Complex.ofReal_natCast, mul_one, add_zero]

theorem evalC_sumProd_fin (ζ : ℕ → ℂ) (n d : ℕ) (f g : ℕ → ℕ × Bool) :
    evalC ζ (sumProd n d f g) = (n : ℂ) * ∑ l : Fin d, litC ζ (f l) * litC ζ (g l) := by
  rw [evalC_sumProd]
  exact congrArg (fun t => (n : ℂ) * t)
    (Fin.sum_univ_eq_sum_range (fun l => litC ζ (f l) * litC ζ (g l)) d).symm

/-- The list of polynomials `F j k` for `j, k < d`. -/
def grid (d : ℕ) (F : ℕ → ℕ → CPoly) : List CPoly :=
  (List.range d).flatMap fun j => (List.range d).map fun k => F j k

theorem forall_mem_grid (d : ℕ) (F : ℕ → ℕ → CPoly) (P : CPoly → Prop) :
    (∀ p ∈ grid d F, P p) ↔ ∀ j, j < d → ∀ k, k < d → P (F j k) := by
  simp only [grid, List.forall_mem_flatMap, List.forall_mem_map, List.mem_range]

/-- Index of the unknown holding entry `(j, k)` of block `(b, e)`. -/
def cv (b e j k : ℕ) : ℕ := Nat.pair b (Nat.pair e (Nat.pair j k))

/-- The Kronecker delta as a natural number. -/
def kdelta (j k : ℕ) : ℕ := if j = k then 1 else 0

theorem kdelta_cast {d : ℕ} (j k : Fin d) :
    ((kdelta j k : ℕ) : ℂ) = (1 : Matrix (Fin d) (Fin d) ℂ) j k := by
  rw [Matrix.one_apply]
  by_cases h : j = k
  · rw [if_pos h, kdelta, if_pos (congrArg Fin.val h), Nat.cast_one]
  · have h2 : ¬((j : ℕ) = (k : ℕ)) := fun h' => h (Fin.ext h')
    rw [if_neg h, kdelta, if_neg h2, Nat.cast_zero]

/-- The `d × d` matrix block `(b, e)` of an assignment. -/
def blk (ζ : ℕ → ℂ) (d b e : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun j k => ζ (cv b e j k)

theorem blk_apply (ζ : ℕ → ℂ) (d b e : ℕ) (j k : Fin d) :
    blk ζ d b e j k = ζ (cv b e j k) := rfl

/-- The vector stored in the first column of block `(b, 0)`. -/
def vec (ζ : ℕ → ℂ) (d b : ℕ) : Fin d → ℂ := fun j => ζ (cv b 0 j 0)

/-- Entry `(p, q)` of the Gram product of two blocks. -/
theorem evalC_sumProd_gram (ζ : ℕ → ℂ) (d b e b' e' : ℕ) (p q : Fin d) :
    evalC ζ (sumProd 1 d (fun l => (cv b e l p, true)) (fun l => (cv b' e' l q, false))) =
      ((blk ζ d b e)ᴴ * blk ζ d b' e') p q := by
  rw [evalC_sumProd_fin, Nat.cast_one, one_mul, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun l _ => rfl

/-- A family of equations indexed by a grid is a matrix identity. -/
theorem grid_iff {ζ : ℕ → ℂ} {d : ℕ} (F : ℕ → ℕ → CPoly) (A B : Matrix (Fin d) (Fin d) ℂ)
    (hF : ∀ j k : Fin d, evalC ζ (F j k) = A j k - B j k) :
    (∀ p ∈ grid d F, evalC ζ p = 0) ↔ A = B := by
  refine (forall_mem_grid d F (fun p => evalC ζ p = 0)).trans ⟨fun h => ?_, fun h j hj k hk => ?_⟩
  · ext j k
    have hjk : evalC ζ (F j k) = 0 := h j j.2 k k.2
    rw [hF] at hjk
    exact sub_eq_zero.mp hjk
  · exact (hF ⟨j, hj⟩ ⟨k, hk⟩).trans (by rw [h, sub_self])

/-- A family of equations indexed by `range d` is a vector identity. -/
theorem range_iff {ζ : ℕ → ℂ} {d : ℕ} (F : ℕ → CPoly) (x y : Fin d → ℂ)
    (hF : ∀ j : Fin d, evalC ζ (F j) = x j - y j) :
    (∀ p ∈ (List.range d).map F, evalC ζ p = 0) ↔ x = y := by
  refine (List.forall_mem_map (P := fun p => evalC ζ p = 0)).trans
    ⟨fun h => ?_, fun h j hj => ?_⟩
  · funext j
    have hj : evalC ζ (F j) = 0 := h j (List.mem_range.mpr j.2)
    rw [hF] at hj
    exact sub_eq_zero.mp hj
  · exact (hF ⟨j, List.mem_range.mp hj⟩).trans (by rw [h, sub_self])

end

end GroupApproximation.Full.NN02c
