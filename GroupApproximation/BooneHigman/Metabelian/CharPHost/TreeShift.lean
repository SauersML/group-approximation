import GroupApproximation.BooneHigman.Metabelian.CharPHost.Carry
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.LinearCombination
import GroupApproximation.Meta.AxiomGuard

/-!
# Letters, shifts and carries of the char-`p` parameter-coordinate host (lane bh-met-02)

Research node `positive-char-polynomial-affine-groups-are-self-similar-proof`, step 4.  The host
ring is `R = F[s_ι]` for a field `F` and a variable index `σ` with a distinguished uniformizer
index `i₀` (bh-met-01 convention: `σ = Fin k`, `i₀ = 0`).  A letter of the tree is a pair
`(e, a)` with `e ∈ F^m` a digit vector and `a ∈ F^{σ ∖ i₀}` a parameter, so for
`F = F_p`, `m = Fin n`, `σ = Fin k` the alphabet is `F_p^n × F_p^(k-1)` as in the node.

This file packages the carry lemma of lane bh-met-01 (`carrySubst`, `carryBase`, `carryQuot`,
`carrySubst_eq_add_carryQuot`, `carryQuot_unique`) in the form used by the tree action:

* `extParam i₀ a`, the parameter extended by `0` at the uniformizer;
* `shift i₀ a`, the carry substitution `σ_a` as a ring endomorphism;
* `digitEval i₀ a`, evaluation at `(0, a)`; `carryDiv i₀ a P`, the quotient `(σ_a P - P(0,a))/s`;
* `shift_eq_add` and the uniqueness statement `shift_unique`;
* `image g b e = g e + b`, with the digit `digit` and carry `carry` of an affine pair at a letter.
-/

noncomputable section

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace CharPHost
namespace TreeHost

open MvPolynomial
open scoped Matrix

variable {F : Type*} [Field F] {σ : Type*} [DecidableEq σ] (i₀ : σ)

/-- The letters `F^m × F^{σ ∖ i₀}` of the tree. -/
abbrev Letter (m F : Type*) {σ : Type*} (i₀ : σ) : Type _ := (m → F) × ({i : σ // i ≠ i₀} → F)

/-- A parameter `a ∈ F^{σ ∖ i₀}`, extended by `0` at the uniformizer index. -/
def extParam (a : {i : σ // i ≠ i₀} → F) (i : σ) : F :=
  if h : i = i₀ then 0 else a ⟨i, h⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.extParam

/-- The carry substitution `σ_a : s_{i₀} ↦ s_{i₀}, s_i ↦ a_i + s_{i₀} s_i`, as a ring hom. -/
def shift (a : {i : σ // i ≠ i₀} → F) : MvPolynomial σ F →+* MvPolynomial σ F :=
  (carrySubst i₀ (extParam i₀ a)).toRingHom

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.shift

/-- Evaluation at the point `(0, a)`. -/
def digitEval (a : {i : σ // i ≠ i₀} → F) : MvPolynomial σ F →+* F :=
  eval (carryBase i₀ (extParam i₀ a))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.digitEval

/-- The carry quotient `(σ_a P - P(0, a)) / s_{i₀}`. -/
def carryDiv (a : {i : σ // i ≠ i₀} → F) (P : MvPolynomial σ F) : MvPolynomial σ F :=
  carryQuot i₀ (extParam i₀ a) P

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.carryDiv

theorem shift_eq_add (a : {i : σ // i ≠ i₀} → F) (P : MvPolynomial σ F) :
    shift i₀ a P = C (digitEval i₀ a P) + X i₀ * carryDiv i₀ a P :=
  carrySubst_eq_add_carryQuot i₀ (extParam i₀ a) P

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.shift_eq_add

theorem shift_C (a : {i : σ // i ≠ i₀} → F) (r : F) : shift i₀ a (C r) = C r := by
  show carrySubst i₀ (extParam i₀ a) (C r) = C r
  rw [MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.shift_C

theorem eval_zero_C_add_X_mul (r : F) (Q : MvPolynomial σ F) :
    eval (0 : σ → F) (C r + X i₀ * Q) = r := by
  rw [map_add, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, Pi.zero_apply, zero_mul,
    add_zero]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.eval_zero_C_add_X_mul

/-- **Uniqueness of digit and carry**: any decomposition `σ_a P = r + s_{i₀} Q` is the canonical
one. -/
theorem shift_unique (a : {i : σ // i ≠ i₀} → F) {P Q : MvPolynomial σ F} {r : F}
    (h : shift i₀ a P = C r + X i₀ * Q) : digitEval i₀ a P = r ∧ carryDiv i₀ a P = Q := by
  have h' := (shift_eq_add i₀ a P).symm.trans h
  have hr : digitEval i₀ a P = r := by
    have h'' := congrArg (eval (0 : σ → F)) h'
    rwa [eval_zero_C_add_X_mul, eval_zero_C_add_X_mul] at h''
  subst hr
  exact ⟨rfl, (carryQuot_unique i₀ (extParam i₀ a) P Q h).symm⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.shift_unique

variable {m : Type*} [Fintype m]

/-- The first-level image `g e + b` of a digit vector `e`, before carrying. -/
def image (g : Matrix m m (MvPolynomial σ F)) (b : m → MvPolynomial σ F) (e : m → F) :
    m → MvPolynomial σ F :=
  g *ᵥ (fun j => C (e j)) + b

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.image

/-- The output digit `g(0, a) e + b(0, a)` of the pair `(g, b)` at the letter `x = (e, a)`. -/
def digit (g : Matrix m m (MvPolynomial σ F)) (b : m → MvPolynomial σ F) (x : Letter m F i₀) :
    m → F :=
  fun j => digitEval i₀ x.2 (image g b x.1 j)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.digit

/-- The carry `(σ_a(g) e + σ_a(b) - c) / s_{i₀}`: the translation part of the state at `x`. -/
def carry (g : Matrix m m (MvPolynomial σ F)) (b : m → MvPolynomial σ F) (x : Letter m F i₀) :
    m → MvPolynomial σ F :=
  fun j => carryDiv i₀ x.2 (image g b x.1 j)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.carry

theorem shift_image (g : Matrix m m (MvPolynomial σ F)) (b : m → MvPolynomial σ F) (e : m → F)
    (a : {i : σ // i ≠ i₀} → F) (j : m) :
    shift i₀ a (image g b e j) = C (digit i₀ g b (e, a) j) + X i₀ * carry i₀ g b (e, a) j :=
  shift_eq_add i₀ a _

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.shift_image

theorem shift_comp_C (a : {i : σ // i ≠ i₀} → F) (c : m → F) :
    (⇑(shift i₀ a) ∘ fun j => C (c j)) = fun j => C (c j) :=
  funext fun j => shift_C i₀ a (c j)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.shift_comp_C

/-- `M (u + s w) = M u + s M w`, entrywise. -/
theorem mulVec_add_X_mul (M : Matrix m m (MvPolynomial σ F)) (u w : m → MvPolynomial σ F) :
    (M *ᵥ fun j => u j + X i₀ * w j) = fun i => (M *ᵥ u) i + X i₀ * (M *ᵥ w) i := by
  funext i
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.mulVec_add_X_mul

end TreeHost
end CharPHost
end Metabelian
end BooneHigman
end GroupApproximation

end
