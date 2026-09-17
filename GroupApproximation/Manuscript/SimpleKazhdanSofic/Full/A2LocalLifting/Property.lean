import GroupApproximation.Analysis.CStarExactness
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.CStarAlgebra.Matrix
import GroupApproximation.Meta.AxiomGuard

/-!
# The local lifting property (table row A2)

`simple_kazhdan_sofic_group.tex`, Introduction, tex l.54–56 (table row A2):

> Ozawa stated the hyperlinear form in 2003, noting that the full $C^*$-algebra of such a group
> cannot have the local lifting property~\cite[\S7]{Ozawa}

This file fixes the notion of "local lifting property" used by row A2.  It is a fork, into lane
`A2LocalLifting`, of the never-wired module `Analysis/LocalLiftingProperty.lean` (which is left
untouched), so that the definitions are compiled from the root.

Ozawa, *About the QWEP conjecture*, Internat. J. Math. **15** (2004), Definition 3.5:

> Let `φ : A → B/J` be a ucp map.  We say `φ` is *locally ucp liftable* if for any finite
> dimensional operator system `E` in `A`, there is a ucp lifting `ψ : E → B`.  We say `A` has the
> LLP (local lifting property) if any ucp map from `A` into any quotient C⋆-algebra `B/J` is
> locally ucp liftable.

A quotient `B/J` is spelled as a surjective ⋆-homomorphism `π : B → C`, and "lifting" means
`π ∘ ψ = φ` on `E`.

* `IsOperatorSystem E`: a complex subspace containing `1` and closed under the star.
* `IsCompletelyPositiveOn E ψ`: complete positivity on an operator system, with ambient
  positivity `star N * N` as in `CStarExactness.IsCompletelyPositive`.
* `IsLocallyUCPLiftable π φ`, `HasLocalLiftingProperty A`: Ozawa's Definition 3.5.
* `OperatorSystemMatrixArvesonStatement`: Arveson's extension theorem for matrix targets (only the
  proposition; its proof is lane `A2OpSys`'s work).

Calibration: `hasLocalLiftingProperty_complex` (`ℂ` has the LLP), so the definition is not
vacuously false.
-/

namespace GroupApproximation
namespace Full
namespace A2LocalLifting

open CStarExactness

universe u v w

section Definitions

variable {A : Type u} [CStarAlgebra A]

/-- An **operator system** in a unital C⋆-algebra: a complex subspace that contains the unit and
is closed under the star. -/
def IsOperatorSystem (E : Submodule ℂ A) : Prop :=
  (1 : A) ∈ E ∧ ∀ x ∈ E, star x ∈ E

/-- **Complete positivity on an operator system.**  For every `n`, a matrix over `E` that is
positive in `Mₙ(A)` is carried entrywise by `ψ` to a positive matrix over the target. -/
def IsCompletelyPositiveOn {B : Type v} [NonUnitalCStarAlgebra B]
    (E : Submodule ℂ A) (ψ : E →ₗ[ℂ] B) : Prop :=
  ∀ (n : ℕ) (M : CStarMatrix (Fin n) (Fin n) E),
    (∃ N : CStarMatrix (Fin n) (Fin n) A,
        M.map (fun x : E ↦ (x : A)) = star N * N) →
      ∃ P : CStarMatrix (Fin n) (Fin n) B, M.map ⇑ψ = star P * P

/-- **Locally ucp liftable** (Ozawa, Definition 3.5).  For every finite-dimensional operator system
`E ⊆ A` there is a unital completely positive `ψ : E → B` with `π ∘ ψ = φ` on `E`. -/
def IsLocallyUCPLiftable {B : Type v} {C : Type w} [CStarAlgebra B]
    [CStarAlgebra C] (π : B →⋆ₐ[ℂ] C) (φ : A →ₗ[ℂ] C) : Prop :=
  ∀ E : Submodule ℂ A, IsOperatorSystem E → FiniteDimensional ℂ E →
    ∃ ψ : E →ₗ[ℂ] B, IsCompletelyPositiveOn E ψ ∧
      (∀ x : E, (x : A) = 1 → ψ x = 1) ∧ ∀ x : E, π (ψ x) = φ x

end Definitions

/-- **The local lifting property** (Ozawa, Definition 3.5; tex l.54–56).  Every unital completely
positive map from `A` into a quotient C⋆-algebra is locally ucp liftable.  A quotient `B/J` is a
surjective ⋆-homomorphism `π : B → C`; the universe `v` of `B` and `C` is a parameter. -/
def HasLocalLiftingProperty (A : Type u) [CStarAlgebra A] : Prop :=
  ∀ (B : Type v) (C : Type v) [CStarAlgebra B] [CStarAlgebra C]
    (π : B →⋆ₐ[ℂ] C), Function.Surjective π →
      ∀ φ : A →ₗ[ℂ] C, IsCompletelyPositive φ → φ 1 = 1 →
        IsLocallyUCPLiftable π φ

/-- **Arveson's extension theorem for matrix targets** (Ozawa, Theorem 2.2, the ucp case): a unital
completely positive map from an operator system of `A` into `B(ℂᵏ)` extends to a unital completely
positive map on all of `A`.  Only the proposition; it is proved by lane `A2OpSys`. -/
def OperatorSystemMatrixArvesonStatement : Prop :=
  ∀ (A : Type u) [CStarAlgebra A] (E : Submodule ℂ A), IsOperatorSystem E →
    ∀ (k : ℕ)
      (ψ : E →ₗ[ℂ] (EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin k))),
      IsCompletelyPositiveOn E ψ → (∀ x : E, (x : A) = 1 → ψ x = 1) →
        ∃ Ψ : A →ₗ[ℂ]
            (EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin k)),
          IsCompletelyPositive (A := A)
              (B := EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin k)) Ψ ∧
            Ψ 1 = 1 ∧ ∀ x : E, Ψ (x : A) = ψ x

section Permanence

variable {A : Type u} [CStarAlgebra A]

/-- A completely positive map restricts to a completely positive map on every operator system. -/
theorem isCompletelyPositiveOn_of_isCompletelyPositive {B : Type v}
    [NonUnitalCStarAlgebra B] {φ : A →ₗ[ℂ] B} (hφ : IsCompletelyPositive φ)
    (E : Submodule ℂ A) : IsCompletelyPositiveOn E (φ.comp E.subtype) := by
  intro n M hM
  obtain ⟨P, hP⟩ := hφ n (M.map fun x : E ↦ (x : A)) hM
  have h : M.map ⇑(φ.comp E.subtype) = (M.map fun x : E ↦ (x : A)).map ⇑φ := by
    ext i j
    rfl
  exact ⟨P, h.trans hP⟩

/-- Completely positive maps on an operator system stay completely positive after a
⋆-homomorphism of the target. -/
theorem isCompletelyPositiveOn_comp_starAlgHom {B : Type v} {C : Type w}
    [CStarAlgebra B] [CStarAlgebra C] {E : Submodule ℂ A} {ψ : E →ₗ[ℂ] B}
    (hψ : IsCompletelyPositiveOn E ψ) (ρ : B →⋆ₐ[ℂ] C) :
    IsCompletelyPositiveOn E
      ((ρ.toNonUnitalStarAlgHom : B →ₗ[ℂ] C).comp ψ) := by
  intro n M hM
  obtain ⟨P, hP⟩ := hψ n M hM
  refine ⟨CStarMatrix.mapₙₐ (n := Fin n) ρ.toNonUnitalStarAlgHom P, ?_⟩
  have h : M.map ⇑((ρ.toNonUnitalStarAlgHom : B →ₗ[ℂ] C).comp ψ)
      = CStarMatrix.mapₙₐ (n := Fin n) ρ.toNonUnitalStarAlgHom (M.map ⇑ψ) := by
    ext i j
    rfl
  rw [h, hP, map_mul, map_star]

end Permanence

/-! ## Calibration: `ℂ` has the local lifting property -/

/-- The `(i, j)` entry of `star N * N` over `ℂ`. -/
theorem complex_star_mul_self_apply {n : ℕ} (N : CStarMatrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    (star N * N) i j = ∑ k : Fin n, star (N k i) * N k j := by
  rw [CStarMatrix.mul_apply]
  exact Finset.sum_congr rfl fun k _ ↦ rfl

/-- **`ℂ` has the local lifting property.**  A unital linear map out of `ℂ` is `z ↦ z • 1`, and so
is its lift `z ↦ z • 1_B` on any operator system of `ℂ`.  Complete positivity is the entrywise
image of a factorization `star N * N` under the ⋆-homomorphism `algebraMap ℂ B`. -/
theorem hasLocalLiftingProperty_complex : HasLocalLiftingProperty.{0, v} ℂ := by
  intro B C _ _ π _ φ _ hφ1 E _ _
  refine ⟨(Algebra.linearMap ℂ B).comp E.subtype, ?_, ?_, ?_⟩
  · intro n M hM
    obtain ⟨N, hN⟩ := hM
    refine ⟨N.map (algebraMap ℂ B), ?_⟩
    have hentry : ∀ i j : Fin n,
        ((M i j : E) : ℂ) = ∑ k : Fin n, star (N k i) * N k j := by
      intro i j
      calc ((M i j : E) : ℂ) = (M.map fun x : E ↦ (x : ℂ)) i j := rfl
        _ = (star N * N) i j :=
          congrArg (fun T : CStarMatrix (Fin n) (Fin n) ℂ ↦ T i j) hN
        _ = ∑ k : Fin n, star (N k i) * N k j := complex_star_mul_self_apply N i j
    ext i j
    calc (M.map ⇑((Algebra.linearMap ℂ B).comp E.subtype)) i j
        = algebraMap ℂ B ((M i j : E) : ℂ) := rfl
      _ = algebraMap ℂ B (∑ k : Fin n, star (N k i) * N k j) := by
        rw [hentry i j]
      _ = ∑ k : Fin n,
            star (algebraMap ℂ B (N k i)) * algebraMap ℂ B (N k j) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        rw [map_mul, algebraMap_star_comm]
      _ = ∑ k : Fin n, (star (N.map (algebraMap ℂ B))) i k
            * (N.map (algebraMap ℂ B)) k j :=
        Finset.sum_congr rfl fun k _ ↦ rfl
      _ = (star (N.map (algebraMap ℂ B)) * N.map (algebraMap ℂ B)) i j :=
        CStarMatrix.mul_apply.symm
  · intro x hx
    show algebraMap ℂ B (x : ℂ) = 1
    rw [hx, map_one]
  · intro x
    calc π ((Algebra.linearMap ℂ B).comp E.subtype x)
        = π (algebraMap ℂ B (x : ℂ)) := rfl
      _ = algebraMap ℂ C (x : ℂ) := AlgHomClass.commutes π (x : ℂ)
      _ = (x : ℂ) • (1 : C) := Algebra.algebraMap_eq_smul_one _
      _ = (x : ℂ) • φ 1 := by rw [hφ1]
      _ = φ ((x : ℂ) • (1 : ℂ)) := (map_smul φ _ _).symm
      _ = φ (x : ℂ) := by rw [smul_eq_mul, mul_one]

end A2LocalLifting
end Full
end GroupApproximation

open GroupApproximation.Full.A2LocalLifting

#audit_axioms IsOperatorSystem
#audit_axioms HasLocalLiftingProperty
#audit_axioms OperatorSystemMatrixArvesonStatement
#audit_closed_axioms hasLocalLiftingProperty_complex
