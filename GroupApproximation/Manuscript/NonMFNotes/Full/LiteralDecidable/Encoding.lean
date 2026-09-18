import GroupApproximation.Manuscript.NonMFNotes.Full.LiteralDecidable.Builders
import Mathlib.Data.Matrix.Mul
import Mathlib.Logic.Equiv.List

/-!
# The polynomial system of the literal predicate (lane NN02c)

Manuscript: `thm:mf-radical-arithmetic` (non_mf_group_notes.tex), sentence
"This is decidable over the real closed field" (Tarski 1951, Seidenberg 1954).

For a code `z = ((c, v), n, d)` we write a system of complex polynomial equations and one
real inequality in unknowns indexed by `cv b e j k`, whose solutions are exactly the matrix
configurations witnessing `NN02b.LiteralD c v n d`:

* block `(0, i)`: the unitary generator `U i` (`Uᴴ U = 1`);
* block `(1, encode u)`: the value of the word `u` (built letter by letter);
* block `(2, encode r)`: `M = 2^(n+10) (W_r - 1)`, and block `(3, encode r)`: a matrix `B`
  with `1 = Mᴴ M + Bᴴ B` (this is `‖W_r - 1‖ ≤ 2^(-n-10)`);
* block `(4, 0)`: a unit vector `x`; block `(5, 0)`: `y = (W_v - 1) x`, with
  `0 ≤ re (4 ⟪y, y⟫ - 1)` (this is `1/2 ≤ ‖W_v - 1‖`).

This file gives the syntax and the translation of every group of equations into the matrix
conditions above.
-/

namespace GroupApproximation.Full.NN02c

open Matrix

noncomputable section

/-- `2^(n+10)`, computed by iterated doubling. -/
def scale (n : ℕ) : ℕ := (fun x : ℕ => 2 * x)^[n] 1024

theorem scale_eq (n : ℕ) : scale n = 2 ^ (n + 10) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h : scale (n + 1) = 2 * scale n :=
      Function.iterate_succ_apply' (fun x : ℕ => 2 * x) n 1024
    rw [h, ih]
    ring

/-! ### Syntax -/

/-- Letter of entry `(j, l)` of the matrix of the letter `a` (generator or its adjoint). -/
def letterLit (g : ℕ) (a : ℕ × Bool) (j l : ℕ) : ℕ × Bool :=
  bif a.2 then (cv 0 (a.1 % g) j l, false) else (cv 0 (a.1 % g) l j, true)

/-- The generators are unitary. -/
def unitaryCons (g d : ℕ) : List CPoly :=
  (List.range g).flatMap fun i => grid d fun p q =>
    diffC (sumProd 1 d (fun l => (cv 0 i l p, true)) (fun l => (cv 0 i l q, false)))
      (constC (kdelta p q))

/-- The empty word has value `1`. -/
def wordBase (d : ℕ) : List CPoly :=
  grid d fun j k =>
    diffC (varC (cv 1 (Encodable.encode ([] : List (ℕ × Bool))) j k, false)) (constC (kdelta j k))

/-- The word `a :: u` has value `letter a * value u`. -/
def wordStep (g d : ℕ) (a : ℕ × Bool) (u : List (ℕ × Bool)) : List CPoly :=
  grid d fun j k =>
    diffC (varC (cv 1 (Encodable.encode (a :: u)) j k, false))
      (sumProd 1 d (fun l => letterLit g a j l) (fun l => (cv 1 (Encodable.encode u) l k, false)))

/-- Equations computing the values of all suffixes of a word. -/
def wordCons (g d : ℕ) : List (ℕ × Bool) → List CPoly
  | [] => wordBase d
  | a :: u => wordStep g d a u ++ wordCons g d u

/-- `M = S (W_r - 1)`. -/
def scaledDefectCons (d S : ℕ) (r : List (ℕ × Bool)) : List CPoly :=
  grid d fun j k =>
    diffC (varC (cv 2 (Encodable.encode r) j k, false))
      (diffC (scaledVarC S (cv 1 (Encodable.encode r) j k, false)) (constC (S * kdelta j k)))

/-- `1 = Mᴴ M + Bᴴ B`. -/
def contractionCons (d : ℕ) (r : List (ℕ × Bool)) : List CPoly :=
  grid d fun j k =>
    diffC (constC (kdelta j k))
      (sumProd 1 d (fun l => (cv 2 (Encodable.encode r) l j, true))
          (fun l => (cv 2 (Encodable.encode r) l k, false)) ++
        sumProd 1 d (fun l => (cv 3 (Encodable.encode r) l j, true))
          (fun l => (cv 3 (Encodable.encode r) l k, false)))

/-- Equations for a relator `r`. -/
def relatorCons (g d S : ℕ) (r : List (ℕ × Bool)) : List CPoly :=
  wordCons g d r ++ (scaledDefectCons d S r ++ contractionCons d r)

/-- `⟪x, x⟫ = 1`. -/
def xNormPoly (d : ℕ) : CPoly :=
  diffC (sumProd 1 d (fun l => (cv 4 0 l 0, true)) (fun l => (cv 4 0 l 0, false))) (constC 1)

/-- Row `j` of `y = W x - x`, where `W` is block `(1, e)`. -/
def yRow (d e j : ℕ) : CPoly :=
  diffC (varC (cv 5 0 j 0, false))
    (diffC (sumProd 1 d (fun l => (cv 1 e j l, false)) (fun l => (cv 4 0 l 0, false)))
      (varC (cv 4 0 j 0, false)))

/-- Equations for the test word `v`. -/
def vCons (g d : ℕ) (v : List (ℕ × Bool)) : List CPoly :=
  wordCons g d v ++ (xNormPoly d :: (List.range d).map (yRow d (Encodable.encode v)))

/-- `4 ⟪y, y⟫ - 1`, required to have nonnegative real part. -/
def vNonneg (d : ℕ) : CPoly :=
  diffC (sumProd 4 d (fun l => (cv 5 0 l 0, true)) (fun l => (cv 5 0 l 0, false))) (constC 1)

/-- The complex system attached to `((c, v), n, d)`. -/
def encodeC (z : ((ℕ × List (List (ℕ × Bool))) × List (ℕ × Bool)) × ℕ × ℕ) : CSystem :=
  (unitaryCons (z.1.1.1 + 1) z.2.2 ++
      (z.1.1.2.flatMap (relatorCons (z.1.1.1 + 1) z.2.2 (scale z.2.1)) ++
        vCons (z.1.1.1 + 1) z.2.2 z.1.2),
    [vNonneg z.2.2])

/-- The neutral real polynomial system attached to `((c, v), n, d)`. -/
def literalSystem (z : ((ℕ × List (List (ℕ × Bool))) × List (ℕ × Bool)) × ℕ × ℕ) :
    PolySystem :=
  compileSystem (encodeC z)

/-! ### Matrix conditions -/

/-- Matrix of the letter `a`: a generator block or its adjoint. -/
def letterMat (ζ : ℕ → ℂ) (g d : ℕ) (a : ℕ × Bool) : Matrix (Fin d) (Fin d) ℂ :=
  bif a.2 then blk ζ d 0 (a.1 % g) else (blk ζ d 0 (a.1 % g))ᴴ

theorem litC_letterLit (ζ : ℕ → ℂ) (g d : ℕ) (a : ℕ × Bool) (j l : Fin d) :
    litC ζ (letterLit g a j l) = letterMat ζ g d a j l := by
  obtain ⟨i, b⟩ := a
  cases b <;> rfl

/-- The block `(1, encode u)` holds the word value of every suffix of `u`. -/
def WordCond (ζ : ℕ → ℂ) (g d : ℕ) : List (ℕ × Bool) → Prop
  | [] => blk ζ d 1 (Encodable.encode ([] : List (ℕ × Bool))) = 1
  | a :: u => blk ζ d 1 (Encodable.encode (a :: u)) =
      letterMat ζ g d a * blk ζ d 1 (Encodable.encode u) ∧ WordCond ζ g d u

/-- Conditions attached to a relator. -/
def RelCond (ζ : ℕ → ℂ) (g d S : ℕ) (r : List (ℕ × Bool)) : Prop :=
  WordCond ζ g d r ∧
    (blk ζ d 2 (Encodable.encode r) = (S : ℂ) • (blk ζ d 1 (Encodable.encode r) - 1) ∧
      1 = (blk ζ d 2 (Encodable.encode r))ᴴ * blk ζ d 2 (Encodable.encode r) +
        (blk ζ d 3 (Encodable.encode r))ᴴ * blk ζ d 3 (Encodable.encode r))

/-- Conditions attached to the test word. -/
def VCond (ζ : ℕ → ℂ) (g d : ℕ) (v : List (ℕ × Bool)) : Prop :=
  WordCond ζ g d v ∧
    (star (vec ζ d 4) ⬝ᵥ vec ζ d 4 = 1 ∧
      vec ζ d 5 = (blk ζ d 1 (Encodable.encode v) - 1) *ᵥ vec ζ d 4)

/-- All conditions of the system. -/
def Solution (ζ : ℕ → ℂ) (z : ((ℕ × List (List (ℕ × Bool))) × List (ℕ × Bool)) × ℕ × ℕ) :
    Prop :=
  ((∀ i, i < z.1.1.1 + 1 → (blk ζ z.2.2 0 i)ᴴ * blk ζ z.2.2 0 i = 1) ∧
      ((∀ r ∈ z.1.1.2, RelCond ζ (z.1.1.1 + 1) z.2.2 (scale z.2.1) r) ∧
        VCond ζ (z.1.1.1 + 1) z.2.2 z.1.2)) ∧
    0 ≤ (((4 : ℕ) : ℂ) * (star (vec ζ z.2.2 5) ⬝ᵥ vec ζ z.2.2 5) - 1).re

/-! ### Translation -/

theorem unitaryCons_iff (ζ : ℕ → ℂ) (g d : ℕ) :
    (∀ p ∈ unitaryCons g d, evalC ζ p = 0) ↔
      ∀ i, i < g → (blk ζ d 0 i)ᴴ * blk ζ d 0 i = 1 := by
  unfold unitaryCons
  refine (List.forall_mem_flatMap (p := fun p => evalC ζ p = 0)).trans
    (forall_congr' fun i => (imp_congr_left List.mem_range).trans
      (imp_congr_right fun _ => ?_))
  exact grid_iff _ _ _ fun p q => by
    rw [evalC_diffC, evalC_sumProd_gram, evalC_constC, kdelta_cast]

theorem wordCons_iff (ζ : ℕ → ℂ) (g d : ℕ) (u : List (ℕ × Bool)) :
    (∀ p ∈ wordCons g d u, evalC ζ p = 0) ↔ WordCond ζ g d u := by
  induction u with
  | nil =>
    show (∀ p ∈ wordBase d, evalC ζ p = 0) ↔
      blk ζ d 1 (Encodable.encode ([] : List (ℕ × Bool))) = 1
    exact grid_iff _ _ _ fun j k => by
      rw [evalC_diffC, evalC_varC, litC_false, evalC_constC, kdelta_cast, blk_apply]
  | cons a u ih =>
    show (∀ p ∈ wordStep g d a u ++ wordCons g d u, evalC ζ p = 0) ↔
      (blk ζ d 1 (Encodable.encode (a :: u)) =
        letterMat ζ g d a * blk ζ d 1 (Encodable.encode u) ∧ WordCond ζ g d u)
    refine (List.forall_mem_append (p := fun p => evalC ζ p = 0)).trans (and_congr ?_ ih)
    exact grid_iff _ _ _ fun j k => by
      rw [evalC_diffC, evalC_varC, litC_false, blk_apply, evalC_sumProd_fin, Nat.cast_one,
        one_mul, Matrix.mul_apply]
      refine congrArg (fun t => ζ (cv 1 (Encodable.encode (a :: u)) j k) - t)
        (Finset.sum_congr rfl fun l _ => ?_)
      rw [litC_letterLit, litC_false, blk_apply]

theorem relatorCons_iff (ζ : ℕ → ℂ) (g d S : ℕ) (r : List (ℕ × Bool)) :
    (∀ p ∈ relatorCons g d S r, evalC ζ p = 0) ↔ RelCond ζ g d S r := by
  refine (List.forall_mem_append (p := fun p => evalC ζ p = 0)).trans
    (and_congr (wordCons_iff ζ g d r) ?_)
  refine (List.forall_mem_append (p := fun p => evalC ζ p = 0)).trans (and_congr ?_ ?_)
  · exact grid_iff _ _ _ fun j k => by
      rw [evalC_diffC, evalC_varC, litC_false, evalC_diffC, evalC_scaledVarC, litC_false,
        evalC_constC, Nat.cast_mul, kdelta_cast, Matrix.smul_apply, Matrix.sub_apply,
        smul_eq_mul, blk_apply, blk_apply]
      ring
  · exact grid_iff _ _ _ fun j k => by
      rw [evalC_diffC, evalC_constC, kdelta_cast, evalC_append, evalC_sumProd_gram,
        evalC_sumProd_gram, Matrix.add_apply]

theorem vCons_iff (ζ : ℕ → ℂ) (g d : ℕ) (v : List (ℕ × Bool)) :
    (∀ p ∈ vCons g d v, evalC ζ p = 0) ↔ VCond ζ g d v := by
  refine (List.forall_mem_append (p := fun p => evalC ζ p = 0)).trans
    (and_congr (wordCons_iff ζ g d v) ?_)
  refine (List.forall_mem_cons (p := fun p => evalC ζ p = 0)).trans (and_congr ?_ ?_)
  · show evalC ζ (xNormPoly d) = 0 ↔ star (vec ζ d 4) ⬝ᵥ vec ζ d 4 = 1
    rw [xNormPoly, evalC_diffC, evalC_sumProd_fin, evalC_constC, Nat.cast_one, one_mul,
      sub_eq_zero]
    exact Iff.rfl
  · exact range_iff _ _ _ fun j => by
      rw [yRow, evalC_diffC, evalC_varC, evalC_diffC, evalC_sumProd_fin, evalC_varC,
        Nat.cast_one, one_mul, Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply]
      rfl

theorem eqs_iff (ζ : ℕ → ℂ) (z : ((ℕ × List (List (ℕ × Bool))) × List (ℕ × Bool)) × ℕ × ℕ) :
    (∀ p ∈ (encodeC z).1, evalC ζ p = 0) ↔
      ((∀ i, i < z.1.1.1 + 1 → (blk ζ z.2.2 0 i)ᴴ * blk ζ z.2.2 0 i = 1) ∧
        ((∀ r ∈ z.1.1.2, RelCond ζ (z.1.1.1 + 1) z.2.2 (scale z.2.1) r) ∧
          VCond ζ (z.1.1.1 + 1) z.2.2 z.1.2)) := by
  show (∀ p ∈ unitaryCons (z.1.1.1 + 1) z.2.2 ++
      (z.1.1.2.flatMap (relatorCons (z.1.1.1 + 1) z.2.2 (scale z.2.1)) ++
        vCons (z.1.1.1 + 1) z.2.2 z.1.2), evalC ζ p = 0) ↔ _
  refine (List.forall_mem_append (p := fun p => evalC ζ p = 0)).trans
    (and_congr (unitaryCons_iff ζ (z.1.1.1 + 1) z.2.2) ?_)
  refine (List.forall_mem_append (p := fun p => evalC ζ p = 0)).trans
    (and_congr ?_ (vCons_iff ζ (z.1.1.1 + 1) z.2.2 z.1.2))
  exact (List.forall_mem_flatMap (p := fun p => evalC ζ p = 0)).trans
    (forall_congr' fun r => imp_congr_right fun _ =>
      relatorCons_iff ζ (z.1.1.1 + 1) z.2.2 (scale z.2.1) r)

theorem vNonneg_iff (ζ : ℕ → ℂ) (d : ℕ) :
    (∀ p ∈ [vNonneg d], 0 ≤ (evalC ζ p).re) ↔
      0 ≤ (((4 : ℕ) : ℂ) * (star (vec ζ d 5) ⬝ᵥ vec ζ d 5) - 1).re := by
  refine (List.forall_mem_singleton (p := fun p => 0 ≤ (evalC ζ p).re)).trans ?_
  show 0 ≤ (evalC ζ (vNonneg d)).re ↔ _
  rw [vNonneg, evalC_diffC, evalC_sumProd_fin, evalC_constC, Nat.cast_one]
  exact Iff.rfl

/-- The complex system of `z` is solvable iff the matrix conditions have a solution. -/
theorem holds_encodeC_iff (z : ((ℕ × List (List (ℕ × Bool))) × List (ℕ × Bool)) × ℕ × ℕ) :
    CSystem.Holds (encodeC z) ↔ ∃ ζ : ℕ → ℂ, Solution ζ z := by
  unfold CSystem.Holds
  exact exists_congr fun ζ => and_congr (eqs_iff ζ z) (vNonneg_iff ζ z.2.2)

end

end GroupApproximation.Full.NN02c
