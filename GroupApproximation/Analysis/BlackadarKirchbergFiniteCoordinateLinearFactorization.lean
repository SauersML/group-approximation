import GroupApproximation.Analysis.BlackadarKirchbergFiniteCoordinateUCP
import Mathlib.LinearAlgebra.Projection
import GroupApproximation.Meta.AxiomGuard

/-!
# Exact finite-coordinate factorization on finite test sets

A finite-dimensional subspace of a function space is determined by finitely
many coordinates.  Consequently, every linear map on a bounded matrix
product factors exactly through a finite coordinate product when restricted
to a prescribed finite test set.

This separates the algebraic part of the Blackadar--Kirchberg localization
from its operator-system content.  Coordinate selection and exact linear
recovery require no approximation.  The remaining density theorem must choose
the finite-coordinate factor to be UCP (or approximate the exact factor by a
UCP one); that positivity assertion is not hidden in this module.
-/

namespace GroupApproximation
namespace BlackadarKirchberg

open scoped Matrix.Norms.L2Operator

noncomputable section

universe u v

/-- A point-separating family of linear maps on a finite-dimensional space
has a finite point-separating subfamily. -/
theorem exists_finset_jointly_injective_of_finiteDimensional
    {E : Type u} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    {I : Type v} {V : I → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (eval : ∀ i, E →ₗ[ℂ] V i)
    (hseparates : ∀ x : E, (∀ i, eval i x = 0) → x = 0) :
    ∃ S : Finset I, ∀ x : E, (∀ i ∈ S, eval i x = 0) → x = 0 := by
  classical
  have aux : ∀ n : ℕ, ∀ p : Submodule ℂ E, Module.finrank ℂ p = n →
      ∃ S : Finset I, ∀ x ∈ p, (∀ i ∈ S, eval i x = 0) → x = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro p hp
        by_cases hpbot : p = ⊥
        · refine ⟨∅, ?_⟩
          intro x hx _
          rw [hpbot] at hx
          exact hx
        · obtain ⟨x, hxp, hxne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hpbot
          have hexists : ∃ i, eval i x ≠ 0 := by
            by_contra h
            push Not at h
            exact hxne (hseparates x h)
          obtain ⟨i, hi⟩ := hexists
          let q : Submodule ℂ E := p ⊓ LinearMap.ker (eval i)
          have hqle : q ≤ p := inf_le_left
          have hxnotq : x ∉ q := by
            intro hxq
            exact hi ((LinearMap.mem_ker).mp ((Submodule.mem_inf).mp hxq).2)
          have hqne : q ≠ p := by
            intro hqp
            exact hxnotq (hqp.symm ▸ hxp)
          have hqlt : q < p := lt_of_le_of_ne hqle hqne
          have hfinrank : Module.finrank ℂ q < n := by
            rw [← hp]
            exact Submodule.finrank_lt_finrank_of_lt hqlt
          obtain ⟨S, hS⟩ := ih (Module.finrank ℂ q) hfinrank q rfl
          refine ⟨insert i S, ?_⟩
          intro y hyp hyzero
          have hyq : y ∈ q := (Submodule.mem_inf).mpr
            ⟨hyp, (LinearMap.mem_ker).mpr (hyzero i (Finset.mem_insert_self i S))⟩
          apply hS y hyq
          intro j hj
          exact hyzero j (Finset.mem_insert_of_mem hj)
  obtain ⟨S, hS⟩ := aux (Module.finrank ℂ E) ⊤ (by simp)
  exact ⟨S, fun x hx ↦ hS x (Submodule.mem_top) hx⟩

/-- Exact finite-coordinate factorization of a linear map out of a
finite-dimensional space. -/
theorem exists_finiteCoordinate_factorization_of_finiteDimensional
    {E : Type u} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    {I : Type v} {V : I → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    {D : Type*} [AddCommGroup D] [Module ℂ D]
    (eval : ∀ i, E →ₗ[ℂ] V i)
    (hseparates : ∀ x : E, (∀ i, eval i x = 0) → x = 0)
    (f : E →ₗ[ℂ] D) :
    ∃ (S : Finset I) (factor : (∀ i : S, V i) →ₗ[ℂ] D),
      ∀ x : E, factor (fun i ↦ eval i x) = f x := by
  classical
  obtain ⟨S, hS⟩ :=
    exists_finset_jointly_injective_of_finiteDimensional eval hseparates
  let coordinates : E →ₗ[ℂ] (∀ i : S, V i) :=
    { toFun := fun x i ↦ eval i x
      map_add' := fun x y ↦ by ext i; exact map_add (eval i) x y
      map_smul' := fun c x ↦ by ext i; exact map_smul (eval i) c x }
  have hcoordinates : Function.Injective coordinates := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply hS (x - y)
    intro i hi
    rw [map_sub]
    have hcoord := congrFun hxy ⟨i, hi⟩
    change eval i x = eval i y at hcoord
    rw [hcoord, sub_self]
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl (LinearMap.range coordinates)
  let back : (∀ i : S, V i) →ₗ[ℂ] E :=
    LinearMap.linearProjOfIsCompl q coordinates hcoordinates hq
  let factor : (∀ i : S, V i) →ₗ[ℂ] D := f.comp back
  refine ⟨S, factor, ?_⟩
  intro x
  dsimp only [factor, LinearMap.comp_apply, back]
  have hcoordinatesApply : (fun i : S ↦ eval i x) = coordinates x := rfl
  rw [hcoordinatesApply, LinearMap.linearProjOfIsCompl_apply_left]

universe w

variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]
variable {D : Type w} [AddCommGroup D] [Module ℂ D]

/-- On a finite set of bounded matrix sequences, every linear map factors
exactly through a finite product of coordinate matrix blocks. -/
theorem exists_finiteCoordinate_linear_factorization
    (F : Finset (BoundedMatrixSequence (fun n ↦ X n)))
    (f : BoundedMatrixSequence (fun n ↦ X n) →ₗ[ℂ] D) :
    ∃ (S : Finset ℕ)
      (factor : (∀ n : S, Matrix (X n) (X n) ℂ) →ₗ[ℂ] D),
      ∀ x ∈ F, factor (fun n ↦ x n) = f x := by
  classical
  let E : Submodule ℂ (BoundedMatrixSequence (fun n ↦ X n)) :=
    Submodule.span ℂ (F : Set (BoundedMatrixSequence (fun n ↦ X n)))
  let eval (n : ℕ) : E →ₗ[ℂ] Matrix (X n) (X n) ℂ :=
    (coordinateEvaluation (fun n ↦ X n) n).comp E.subtype
  have hseparates : ∀ x : E, (∀ n, eval n x = 0) → x = 0 := by
    intro x hx
    apply Subtype.ext
    apply lp.ext
    funext n
    exact hx n
  let fE : E →ₗ[ℂ] D := f.comp E.subtype
  obtain ⟨S, factor, hfactor⟩ :=
    exists_finiteCoordinate_factorization_of_finiteDimensional eval hseparates fE
  refine ⟨S, factor, ?_⟩
  intro x hx
  let xE : E := ⟨x, Submodule.subset_span hx⟩
  calc
    factor (fun n ↦ x n) = factor (fun n ↦ eval n xE) := by
      congr 1
    _ = fE xE := hfactor xE
    _ = f x := rfl

end

end BlackadarKirchberg
end GroupApproximation

open GroupApproximation.BlackadarKirchberg

#audit_axioms exists_finset_jointly_injective_of_finiteDimensional
#audit_axioms exists_finiteCoordinate_factorization_of_finiteDimensional
#audit_axioms exists_finiteCoordinate_linear_factorization
