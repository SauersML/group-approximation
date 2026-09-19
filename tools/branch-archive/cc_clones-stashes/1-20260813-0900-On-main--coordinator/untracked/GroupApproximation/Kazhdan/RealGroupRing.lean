import GroupApproximation.Kazhdan.GroupRingLaplacian
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.MapDomain

/-!
# A small exact real group-ring evaluator

This file gives the algebraic layer needed by machine-checkable
sum-of-squares certificates.  The representation of a group-ring element is
defined directly as a finite sum, so a certificate can be stored as exact
finitely supported rational or integer data and its identity can be checked
without trusting a numerical solver.
-/

namespace GroupApproximation
namespace RealGroupRing

open scoped InnerProductSpace

universe u v

variable {G : Type u} [Group G]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The real group ring, represented by finitely supported coefficients. -/
abbrev Element (G : Type u) := MonoidAlgebra ℝ G

/-- Convolution product, written explicitly so certificate evaluation does
not depend on a hidden normalization convention. -/
noncomputable def convolution (a b : Element G) : Element G := a * b

/-- The real group-ring involution induced by group inversion. -/
noncomputable def adjoint (a : Element G) : Element G :=
  MonoidAlgebra.mapDomain (fun g ↦ g⁻¹) a

@[simp] theorem adjoint_zero : adjoint (0 : Element G) = 0 := by
  simp [adjoint]

@[simp] theorem adjoint_single (g : G) (c : ℝ) :
    adjoint (MonoidAlgebra.single g c) =
      MonoidAlgebra.single g⁻¹ c := by
  simp [adjoint]

@[simp] theorem adjoint_add (a b : Element G) :
    adjoint (a + b) = adjoint a + adjoint b := by
  exact MonoidAlgebra.mapDomain_add _ _ _

@[simp] theorem adjoint_sub (a b : Element G) :
    adjoint (a - b) = adjoint a - adjoint b := by
  apply eq_sub_iff_add_eq.mpr
  rw [← adjoint_add]
  congr 1
  abel

@[simp] theorem adjoint_finset_sum {ι : Type*} (s : Finset ι)
    (a : ι → Element G) :
    adjoint (∑ i ∈ s, a i) = ∑ i ∈ s, adjoint (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih]

/-- An orthogonal representation regarded as a representation by linear
endomorphisms. -/
def endRepresentation (ρ : G →* (E ≃ₗᵢ[ℝ] E)) :
    G →* Module.End ℝ E where
  toFun g := (ρ g).toLinearEquiv.toLinearMap
  map_one' := by
    ext x
    simp
  map_mul' g h := by
    ext x
    simp

/-- The algebra homomorphism obtained by extending a group representation
linearly to the real group ring. -/
noncomputable def operator (ρ : G →* (E ≃ₗᵢ[ℝ] E)) :
    Element G →ₐ[ℝ] Module.End ℝ E :=
  MonoidAlgebra.lift ℝ (Module.End ℝ E) G (endRepresentation ρ)

/-- Evaluation of a real group-ring element in an orthogonal
representation, on one vector. -/
noncomputable def evaluate (a : Element G)
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) : E :=
  operator ρ a x

@[simp] theorem evaluate_zero (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    evaluate (0 : Element G) ρ x = 0 := by
  simp [evaluate]

@[simp] theorem evaluate_single (g : G) (c : ℝ)
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    evaluate (MonoidAlgebra.single g c) ρ x = c • ρ g x := by
  simp [evaluate, operator, endRepresentation]

@[simp] theorem evaluate_add (a b : Element G)
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    evaluate (a + b) ρ x = evaluate a ρ x + evaluate b ρ x := by
  simp [evaluate]

@[simp] theorem evaluate_sub (a b : Element G)
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    evaluate (a - b) ρ x = evaluate a ρ x - evaluate b ρ x := by
  simp [evaluate]

@[simp] theorem evaluate_finset_sum {ι : Type*} (s : Finset ι)
    (a : ι → Element G) (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    evaluate (∑ i ∈ s, a i) ρ x = ∑ i ∈ s, evaluate (a i) ρ x := by
  simp [evaluate]

@[simp] theorem evaluate_smul (c : ℝ) (a : Element G)
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    evaluate (c • a) ρ x = c • evaluate a ρ x := by
  simp [evaluate]

@[simp] theorem evaluate_convolution (a b : Element G)
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    evaluate (convolution a b) ρ x = evaluate a ρ (evaluate b ρ x) := by
  change operator ρ (a * b) x = operator ρ a (operator ρ b x)
  rw [map_mul]
  rfl

/-- Evaluating the adjoint transfers the group-ring operator across the real
inner product. -/
theorem inner_evaluate_adjoint (a : Element G)
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x y : E) :
    inner ℝ x (evaluate (adjoint a) ρ y) =
      inner ℝ (evaluate a ρ x) y := by
  classical
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp [adjoint]
  | add a b ha hb =>
      rw [adjoint, MonoidAlgebra.mapDomain_add]
      rw [evaluate_add, inner_add_right, evaluate_add, inner_add_left]
      exact congrArg₂ (· + ·) (by simpa [adjoint] using ha)
        (by simpa [adjoint] using hb)
  | single g c =>
      rw [adjoint, MonoidAlgebra.mapDomain_single]
      rw [evaluate_single, evaluate_single]
      rw [real_inner_smul_right, real_inner_smul_left]
      congr 1
      have h := (ρ g).inner_map_map x (ρ g⁻¹ y)
      simpa using h.symm

/-- Every Hermitian square has nonnegative quadratic form; in fact its
quadratic form is exactly the squared norm of the evaluated factor. -/
theorem inner_evaluate_adjoint_convolution_self (a : Element G)
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    inner ℝ x (evaluate (convolution (adjoint a) a) ρ x) =
      ‖evaluate a ρ x‖ ^ 2 := by
  rw [evaluate_convolution, inner_evaluate_adjoint]
  exact real_inner_self_eq_norm_sq _

/-- The group-ring element `sum_{s in S} (1-s)`. -/
noncomputable def laplacianElement (S : Finset G) : Element G :=
  ∑ g ∈ S,
    (MonoidAlgebra.single 1 1 - MonoidAlgebra.single g 1)

/-- The algebraic Laplacian evaluates to the analytic Laplacian used by the
Kazhdan spectral-gap interface. -/
theorem evaluate_laplacianElement (S : Finset G)
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    evaluate (laplacianElement S) ρ x =
      GroupRingLaplacian.laplacian S ρ x := by
  classical
  rw [GroupRingLaplacian.laplacian_apply]
  simp [laplacianElement, Nat.cast_smul_eq_nsmul]

/-- An inverse-closed finite set has an algebraically self-adjoint
Laplacian. -/
theorem adjoint_laplacianElement_of_inv_closed
    (S : Finset G) (hinv : ∀ g, g ∈ S ↔ g⁻¹ ∈ S) :
    adjoint (laplacianElement S) = laplacianElement S := by
  classical
  rw [laplacianElement, adjoint_finset_sum]
  simp only [adjoint_sub, adjoint_single, inv_one]
  apply Finset.sum_bij (fun g _ ↦ g⁻¹)
  · intro g hg
    exact (hinv g).mp hg
  · intro a ha b hb hab
    exact inv_injective hab
  · intro g hg
    refine ⟨g⁻¹, (hinv g⁻¹).mpr ?_, by simp⟩
    simpa using hg
  · intro g hg
    simp

/-! ## Exact sum-of-squares certificates -/

/-- A finite exact certificate for the quadratic inequality
`c * <x, Δx> ≤ ||Δx||²`.  Its identity is entirely algebraic:

`Δ* Δ - c Δ = sum_i ξ_i* ξ_i`.

The use of `Δ* Δ` makes the definition valid without separately assuming
that the chosen finite set is inverse-closed. -/
def IsSOSQuadraticGap (S : Finset G) (c : ℝ) : Prop :=
  ∃ n : ℕ, ∃ factor : Fin n → Element G,
    convolution (adjoint (laplacianElement S)) (laplacianElement S) -
        c • laplacianElement S =
      ∑ i, convolution (adjoint (factor i)) (factor i)

/-- An exact group-ring SOS identity implies the associated quadratic
operator gap in every orthogonal representation. -/
theorem quadratic_gap_of_sos
    (S : Finset G) {c : ℝ} (hcert : IsSOSQuadraticGap S c)
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    c * inner ℝ x (GroupRingLaplacian.laplacian S ρ x) ≤
      ‖GroupRingLaplacian.laplacian S ρ x‖ ^ 2 := by
  classical
  obtain ⟨n, factor, hidentity⟩ := hcert
  have heq := congrArg
    (fun a : Element G ↦ inner ℝ x (evaluate a ρ x)) hidentity
  rw [evaluate_sub, inner_sub_right,
    inner_evaluate_adjoint_convolution_self, evaluate_smul,
    real_inner_smul_right] at heq
  rw [evaluate_finset_sum, inner_sum] at heq
  simp_rw [inner_evaluate_adjoint_convolution_self] at heq
  rw [evaluate_laplacianElement] at heq
  have hnonneg : 0 ≤ ∑ i : Fin n, ‖evaluate (factor i) ρ x‖ ^ 2 := by
    exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  nlinarith

end RealGroupRing
end GroupApproximation
