import GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeWord
import GroupApproximation.BooneHigman.Metabelian.CharPHost.CarryRecursion
import Mathlib.Algebra.Polynomial.AlgebraMap
import GroupApproximation.Meta.AxiomGuard

/-!
# Evaluating the tree action along a line (lane bh-met-02)

Faithfulness step of lane bh-met-02.  Evaluate `F[s_σ]` into `F[X]` by `s_{i₀} ↦ X`,
`s_i ↦ A_i` (`ev i₀ A`, via bh-met-01's `withUniformizer`).  A word
`(e_1, a_1) ⋯ (e_j, a_j)` with a tail vector `v ∈ F[X]^m` gives the vector
`vecOf w v = e_1 + X (e_2 + ⋯ + X (e_j + X v))`, and the parameters of `w` move the point `A` to
`listPoint X (params w) A` (bh-met-01).  The identity

  `g(X, listPoint w A) · vecOf w v + b(X, listPoint w A) = vecOf (act g b w) R`

for some tail `R` (`exists_vecOf_act`) says that the tree action is the `X`-adic expansion of the
affine map `(g, b)` restricted to the line through `listPoint w A`.

Main declarations: `ev`, `ev_shift` (bh-met-01's `aeval_carrySubst`), `vecOf`, `params`,
`eval_step`, `exists_vecOf_act`.
-/

noncomputable section

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace CharPHost
namespace TreeHost

open MvPolynomial
open scoped Matrix Polynomial

/-- `M (u + t w) = M u + t M w`, entrywise. -/
theorem mulVec_add_mul {S : Type*} [CommRing S] {m : Type*} [Fintype m] (M : Matrix m m S)
    (u w : m → S) (t : S) (i : m) :
    (M *ᵥ fun j => u j + t * w j) i = (M *ᵥ u) i + t * (M *ᵥ w) i := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.mulVec_add_mul

variable {F : Type*} [Field F] {σ : Type*} [DecidableEq σ] (i₀ : σ)

/-- Evaluation `s_{i₀} ↦ X`, `s_i ↦ A_i` into `F[X]`. -/
def ev (A : σ → F[X]) : MvPolynomial σ F →+* F[X] :=
  (aeval (withUniformizer i₀ Polynomial.X A)).toRingHom

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.ev

/-- bh-met-01's substitution identity: `σ_a(Q)(X, A) = Q(X, a + X A)`. -/
theorem ev_shift (a : {i : σ // i ≠ i₀} → F) (A : σ → F[X]) (Q : MvPolynomial σ F) :
    ev i₀ A (shift i₀ a Q) = ev i₀ (shiftPoint (extParam i₀ a) Polynomial.X A) Q :=
  aeval_carrySubst i₀ (extParam i₀ a) Polynomial.X A Q

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.ev_shift

theorem ev_C (A : σ → F[X]) (r : F) : ev i₀ A (C r) = Polynomial.C r := by
  show aeval (withUniformizer i₀ Polynomial.X A) (C r) = Polynomial.C r
  rw [aeval_C, Polynomial.algebraMap_eq]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.ev_C

theorem ev_X_self (A : σ → F[X]) : ev i₀ A (X i₀) = Polynomial.X := by
  show aeval (withUniformizer i₀ Polynomial.X A) (X i₀) = Polynomial.X
  rw [aeval_X]
  exact if_pos (rfl : i₀ = i₀)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.ev_X_self

theorem ev_comp_C {m : Type*} (A : σ → F[X]) (c : m → F) :
    (⇑(ev i₀ A) ∘ fun j => C (c j)) = fun j => Polynomial.C (c j) :=
  funext fun j => ev_C i₀ A (c j)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.ev_comp_C

variable {m : Type*} [Fintype m]

/-- The vector `e_1 + X (e_2 + ⋯ + X (e_j + X v))` of a word `w` with tail `v`. -/
def vecOf : List (Letter m F i₀) → (m → F[X]) → m → F[X]
  | [], v => v
  | x :: w, v => fun k => Polynomial.C (x.1 k) + Polynomial.X * vecOf w v k

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.vecOf

/-- The parameters of a word, extended by `0` at the uniformizer. -/
def params (w : List (Letter m F i₀)) : List (σ → F) :=
  w.map fun x => extParam i₀ x.2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.params

/-- One letter of `exists_vecOf_act`: the digit and carry of `(g, b)` at `(e, a)` evaluated along
the line through `a + X P`. -/
theorem eval_step (g : Matrix m m (MvPolynomial σ F)) (b : m → MvPolynomial σ F) (e : m → F)
    (a : {i : σ // i ≠ i₀} → F) (P : σ → F[X]) (V : m → F[X]) (k : m) :
    (g.map (ev i₀ (shiftPoint (extParam i₀ a) Polynomial.X P)) *ᵥ
        fun j => Polynomial.C (e j) + Polynomial.X * V j) k +
      ev i₀ (shiftPoint (extParam i₀ a) Polynomial.X P) (b k) =
      Polynomial.C (digit i₀ g b (e, a) k) + Polynomial.X *
        (((g.map (shift i₀ a)).map (ev i₀ P) *ᵥ V) k + ev i₀ P (carry i₀ g b (e, a) k)) := by
  have hmat : (g.map (shift i₀ a)).map (ev i₀ P) =
      g.map (ev i₀ (shiftPoint (extParam i₀ a) Polynomial.X P)) :=
    Matrix.ext fun i j => by
      rw [Matrix.map_apply, Matrix.map_apply, Matrix.map_apply]
      exact ev_shift i₀ a P (g i j)
  have h1 := congrArg (ev i₀ P) (shift_image i₀ g b e a k)
  rw [ev_shift, image, Pi.add_apply, map_add, map_add, RingHom.map_mulVec, ev_comp_C, map_mul,
    ev_C, ev_X_self] at h1
  rw [mulVec_add_mul, hmat]
  linear_combination h1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.eval_step

/-- **The tree action is the `X`-adic expansion of the affine map along a line**: evaluating
`(g, b)` at the point reached along `w` and applying it to `vecOf w v` gives `vecOf (act g b w) R`
for some tail `R`. -/
theorem exists_vecOf_act (w : List (Letter m F i₀)) :
    ∀ (g : Matrix m m (MvPolynomial σ F)) (b : m → MvPolynomial σ F) (A : σ → F[X])
      (v : m → F[X]), ∃ R : m → F[X], ∀ k,
        (g.map (ev i₀ (listPoint Polynomial.X (params i₀ w) A)) *ᵥ vecOf i₀ w v) k +
          ev i₀ (listPoint Polynomial.X (params i₀ w) A) (b k) = vecOf i₀ (act i₀ g b w) R k := by
  induction w with
  | nil =>
    intro g b A v
    exact ⟨fun k => (g.map (ev i₀ A) *ᵥ v) k + ev i₀ A (b k), fun k => rfl⟩
  | cons x u ih =>
    intro g b A v
    obtain ⟨e, a⟩ := x
    obtain ⟨R, hR⟩ := ih (g.map (shift i₀ a)) (carry i₀ g b (e, a)) A v
    exact ⟨R, fun k =>
      (eval_step i₀ g b e a (listPoint Polynomial.X (params i₀ u) A) (vecOf i₀ u v) k).trans
        (congrArg (fun t : F[X] => Polynomial.C (digit i₀ g b (e, a) k) + Polynomial.X * t) (hR k))⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.exists_vecOf_act

end TreeHost
end CharPHost
end Metabelian
end BooneHigman
end GroupApproximation

end
