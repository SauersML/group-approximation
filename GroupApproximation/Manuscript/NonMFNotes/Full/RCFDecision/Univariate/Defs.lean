import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.Real.Basic

/-!
# Univariate real sign calculus: the vocabulary of the decision procedure

`non_mf_group_notes.tex`, `thm:mf-arithmetic`, proof: "Fixed-dimensional
feasibility is decidable over the real closed field."  The decision procedure
formalized in `RCFDecision/` is Tarski's, in the Sturm--Tarski /
Ben-Or--Kozen--Reif form (Basu--Pollack--Roy, *Algorithms in Real Algebraic
Geometry*, Ch. 2 and Ch. 10).  This file only fixes the semantic vocabulary
over `ℝ[X]`:

* `sgn`, the sign of a real number, and `sgnVec`, a sign vector;
* `taq Q P`, the Tarski query `∑_{P(x)=0} sgn Q(x)`;
* `changes`, the number of sign changes of a list of nonzero signs;
* `sgnTop` / `sgnBot`, the sign of a polynomial at `+∞` / `-∞`;
* `SturmChain`, a generalized signed remainder sequence: consecutive
  triples satisfy `c·A = S·B - d·D` with `c, d > 0` and `deg D < deg B`,
  and the last element divides the one before;
* `weight`, `prodPow`, `expVecs`, `bkrSum`: the Ben-Or--Kozen--Reif sign
  determination sum.
-/

namespace GroupApproximation.Full.NN11b

open Polynomial

noncomputable section

/-- The sign of a real number, as an integer in `{-1, 0, 1}`. -/
def sgn (x : ℝ) : ℤ := if 0 < x then 1 else if x < 0 then -1 else 0

/-- The sign vector of a list of polynomials at a point. -/
def sgnVec (ps : List ℝ[X]) (x : ℝ) : List ℤ := ps.map fun p => sgn (p.eval x)

/-- The Tarski query `TaQ(Q, P) = ∑_{x ∈ ℝ, P(x) = 0} sgn Q(x)` (BPR, Def. 2.54). -/
def taq (Q P : ℝ[X]) : ℤ := ∑ x ∈ P.roots.toFinset, sgn (Q.eval x)

/-- Number of sign changes between consecutive entries of a list of signs. -/
def changes : List ℤ → ℕ
  | a :: b :: l => (if a * b < 0 then 1 else 0) + changes (b :: l)
  | _ => 0

/-- The sign of a polynomial at `+∞`. -/
def sgnTop (p : ℝ[X]) : ℤ := sgn p.leadingCoeff

/-- The sign of a polynomial at `-∞`. -/
def sgnBot (p : ℝ[X]) : ℤ := sgn (p.leadingCoeff * (-1) ^ p.natDegree)

/-- One generalized signed-remainder step: `c·A = S·B - d·D` with `c, d > 0`
and `deg D < deg B`. -/
def RemStep (A B D : ℝ[X]) : Prop :=
  ∃ c d : ℝ, 0 < c ∧ 0 < d ∧ ∃ S : ℝ[X], C c * A = S * B - C d * D ∧ D.degree < B.degree

/-- A generalized Sturm chain (signed remainder sequence up to positive
multipliers, BPR Def. 1.7 / 2.56): consecutive triples are `RemStep`s and the
last element divides the one before it. -/
def SturmChain : List ℝ[X] → Prop
  | A :: B :: D :: l => RemStep A B D ∧ SturmChain (B :: D :: l)
  | [A, B] => B ∣ A
  | _ => True

/-- The entry `w(s, k)` of `2·M⁻¹`, where `M = [[1,1,1],[0,1,-1],[0,1,1]]` is the
Ben-Or--Kozen--Reif matrix (rows: exponent `k ∈ {0,1,2}`, columns: sign
`s ∈ {0,1,-1}`).  It satisfies `∑_{k ≤ 2} w(s, k) t^k = 2·[t = s]` for
`s, t ∈ {-1, 0, 1}`. -/
def weight1 (s : ℤ) (k : ℕ) : ℤ :=
  if s = 0 then (if k = 0 then 2 else if k = 1 then 0 else -2)
  else if s = 1 then (if k = 0 then 0 else 1)
  else (if k = 0 then 0 else if k = 1 then -1 else 1)

/-- The product weight `∏_j w(σ_j, e_j)`. -/
def weight : List ℤ → List ℕ → ℤ
  | s :: σ, k :: e => weight1 s k * weight σ e
  | _, _ => 1

/-- The product `∏_j q_j^{e_j}`. -/
def prodPow : List ℝ[X] → List ℕ → ℝ[X]
  | q :: qs, k :: e => q ^ k * prodPow qs e
  | _, _ => 1

/-- All exponent vectors in `{0,1,2}^m`. -/
def expVecs : ℕ → List (List ℕ)
  | 0 => [[]]
  | m + 1 => (expVecs m).flatMap fun e => [0 :: e, 1 :: e, 2 :: e]

/-- The Ben-Or--Kozen--Reif sum `∑_{e ∈ {0,1,2}^m} w(σ, e) · TaQ(∏ q_j^{e_j}, P)`. -/
def bkrSum (P : ℝ[X]) (qs : List ℝ[X]) (σ : List ℤ) : ℤ :=
  ((expVecs qs.length).map fun e => weight σ e * taq (prodPow qs e) P).sum

end

end GroupApproximation.Full.NN11b
