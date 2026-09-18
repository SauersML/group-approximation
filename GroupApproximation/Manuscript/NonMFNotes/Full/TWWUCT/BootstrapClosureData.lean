import GroupApproximation.Manuscript.NonMFNotes.Full.TWWUCT.BootstrapClosureBasic
import GroupApproximation.Analysis.CStarExactness

/-!
# Semisplit extensions and sequential inductive limits

The two non-formal closure properties of the Rosenberg--Schochet class (Duke Math. J. 55 (1987),
§§2--4; Blackadar, *K-Theory for Operator Algebras*, 19.5, 22.3.4--22.3.5) concern

* **semisplit extensions** `0 → I → A → B → 0`: the quotient map has a completely positive
  contractive linear section (Blackadar 15.8, 19.5.1); for these the six-term exact sequences in
  `KK` exist, and the class has the two-out-of-three property;
* **countable inductive limits** `A₁ → A₂ → ⋯ → L` (Blackadar 19.7.1, 22.3.4).

This file only fixes the data these statements are about.  An inductive limit is described
intrinsically: compatible maps `ψ n : A n → L` with dense union of ranges and the norm formula
`‖ψ n a‖ = lim_m ‖φ_{n,n+m} a‖`, which characterizes the C⋆-inductive limit up to
isomorphism.

Manuscript: `non_mf_group_notes.tex`, UCT input of `thm:fixed-radical-membership`.
-/

namespace GroupApproximation.Full.TWWUCT.Bootstrap

noncomputable section

/-- **A semisplit extension** `0 → I → A → B → 0` of separable non-unital C⋆-algebras. -/
structure SemisplitExtension (I A B : SepNUCStarAlgebra) where
  /-- The inclusion of the ideal. -/
  incl : I →⋆ₙₐ[ℂ] A
  /-- The quotient map. -/
  quot : A →⋆ₙₐ[ℂ] B
  incl_injective : Function.Injective incl
  quot_surjective : Function.Surjective quot
  /-- Exactness in the middle. -/
  exact : ∀ a : A, quot a = 0 ↔ ∃ i : I, incl i = a
  /-- The completely positive contractive section. -/
  sec : B →ₗ[ℂ] A
  sec_completelyPositive : CStarExactness.IsCompletelyPositive sec
  sec_contractive : ∀ b : B, ‖sec b‖ ≤ ‖b‖
  quot_sec : ∀ b : B, quot (sec b) = b

/-- The connecting maps `φ_{n,n+m} : A n → A (n + m)` of an inductive system. -/
def connecting {A : ℕ → SepNUCStarAlgebra} (φ : ∀ n : ℕ, A n →⋆ₙₐ[ℂ] A (n + 1)) (n : ℕ) :
    ∀ m : ℕ, A n →⋆ₙₐ[ℂ] A (n + m)
  | 0 => NonUnitalStarAlgHom.id ℂ (A n)
  | m + 1 => (φ (n + m)).comp (connecting φ n m)

/-- **`L` is the C⋆-inductive limit** of the system `(A n, φ n)`, witnessed by the canonical
maps `ψ n : A n → L`. -/
structure SeqInductiveLimit (A : ℕ → SepNUCStarAlgebra) (φ : ∀ n : ℕ, A n →⋆ₙₐ[ℂ] A (n + 1))
    (L : SepNUCStarAlgebra) where
  /-- The canonical maps into the limit. -/
  ψ : ∀ n : ℕ, A n →⋆ₙₐ[ℂ] L
  /-- Compatibility with the connecting maps. -/
  compat : ∀ (n : ℕ) (a : A n), ψ (n + 1) (φ n a) = ψ n a
  /-- The union of the ranges is dense. -/
  dense : Dense (⋃ n : ℕ, Set.range (ψ n))
  /-- The norm formula. -/
  norm_tendsto : ∀ (n : ℕ) (a : A n),
    Filter.Tendsto (fun m : ℕ => ‖connecting φ n m a‖) Filter.atTop (nhds ‖ψ n a‖)

end

end GroupApproximation.Full.TWWUCT.Bootstrap
