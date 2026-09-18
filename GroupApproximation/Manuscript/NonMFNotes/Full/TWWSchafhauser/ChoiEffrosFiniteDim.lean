import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ChoiEffrosNormalize
import GroupApproximation.Analysis.FiniteDimensionalCStarMatrixCPRetract

/-!
# Choi–Effros lifting, finite-dimensional domains

Lane `TWWSchafhauser-3a` (work order `WO-TWWCore-3`, piece 3a).

Let `π : B → C` be a surjective `⋆`-homomorphism of unital C⋆-algebras.

* `exists_cp_matrix_lift` — a completely positive map `M_k(ℂ) → C` lifts to a
  completely positive map `M_k(ℂ) → B`: factor its Choi matrix as `P⋆P`, lift
  the finitely many entries of `P` along `π`, and take the Gram-family Choi map
  of the lifted entries.  This is the argument of
  `BlackadarKirchberg.exists_completelyPositive_matrix_lift`, stated for an
  arbitrary surjection instead of the concrete matrix corona.
* `exists_cp_lift_of_finiteDimensional` — the same for a nontrivial
  finite-dimensional domain `D`, through a matrix unital cp retract
  `D → M_n(ℂ) → D` (`BlackadarKirchberg.exists_matrixUCPRetract_of_finiteDimensionalCStar`).
* `exists_cpc_lift_of_finiteDimensional` — completely positive *contractive*
  maps out of a finite-dimensional domain lift to completely positive
  contractive maps (normalization by `exists_cpc_lift_of_cp_lift`).
* `exists_cpc_approx_lift_of_isNuclearMap` — a nuclear map `A → C` is
  point-norm approximately liftable by completely positive contractions: lift
  the finite-dimensional factor of each approximate factorization.

Sources: M.-D. Choi, E. G. Effros, *The completely positive lifting problem for
C⋆-algebras*, Ann. of Math. (2) **104** (1976), 585–609, Lemma 3.9 and the
proof of Theorem 3.10; N. P. Brown, N. Ozawa, *C⋆-algebras and
finite-dimensional approximations*, Lemma C.2 and the proof of Theorem C.3.
-/

namespace GroupApproximation
namespace Full
namespace TWWSchafhauser

open scoped Matrix.Norms.L2Operator

noncomputable section

universe u v w

local instance choiEffrosMatrixCStarAlgebra (Z : Type*) [Fintype Z] [DecidableEq Z]
    [Nonempty Z] : CStarAlgebra (Matrix Z Z ℂ) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

/-- Reindexing rows and columns by one equivalence is a `⋆`-algebra
equivalence of complex matrix algebras. -/
def choiEffrosMatrixReindex {m n : Type} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (e : m ≃ n) : Matrix m m ℂ ≃⋆ₐ[ℂ] Matrix n n ℂ :=
  StarAlgEquiv.ofAlgEquiv (Matrix.reindexAlgEquiv ℂ ℂ e) (by
    intro A
    ext i j
    rfl)

/-! ## Full matrix domains -/

/-- **Completely positive lifting out of a full matrix algebra.**  Every
completely positive map `M_k(ℂ) → C` has a completely positive lift through a
surjective `⋆`-homomorphism `π : B → C` (Choi–Effros, Lemma 3.9). -/
theorem exists_cp_matrix_lift {B : Type v} {C : Type w} [CStarAlgebra B] [CStarAlgebra C]
    (π : B →⋆ₐ[ℂ] C) (hπ : Function.Surjective π) {k : ℕ} [Nonempty (Fin k)]
    (f : Matrix (Fin k) (Fin k) ℂ →ₗ[ℂ] C) (hf : CStarExactness.IsCompletelyPositive f) :
    ∃ lift : Matrix (Fin k) (Fin k) ℂ →ₗ[ℂ] B,
      CStarExactness.IsCompletelyPositive lift ∧ ∀ T, π (lift T) = f T := by
  obtain ⟨P, hP⟩ := BlackadarKirchberg.exists_factor_choiMatrix_of_cp f hf
  choose R hR using fun s i : Fin k ↦ hπ (P s i)
  refine ⟨BlackadarKirchberg.matrixGramChoiMap R,
    BlackadarKirchberg.isCompletelyPositive_matrixGramChoiMap R, fun T ↦ ?_⟩
  have hentry : ∀ i j : Fin k,
      π (∑ s : Fin k, star (R s i) * R s j) = f (Matrix.single i j 1) := by
    intro i j
    have h : BlackadarKirchberg.choiMatrix f i j = (star P * P) i j := by rw [hP]
    rw [BlackadarKirchberg.choiMatrix_apply, CStarExactness.cstarMatrix_mul_apply] at h
    rw [h, map_sum]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [map_mul, map_star, hR, hR, CStarExactness.cstarMatrix_star_apply]
  rw [BlackadarKirchberg.matrixGramChoiMap_apply, map_sum]
  calc (∑ p : Fin k, π (∑ q : Fin k, T p q • ∑ s : Fin k, star (R s p) * R s q))
      = ∑ p : Fin k, ∑ q : Fin k, T p q • f (Matrix.single p q 1) := by
        refine Finset.sum_congr rfl fun p _ ↦ ?_
        rw [map_sum]
        refine Finset.sum_congr rfl fun q _ ↦ ?_
        rw [map_smul, hentry]
    _ = f (∑ p : Fin k, ∑ q : Fin k, T p q • Matrix.single p q 1) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun p _ ↦ ?_
        rw [map_sum]
        exact Finset.sum_congr rfl fun q _ ↦ (map_smul f (T p q) (Matrix.single p q 1)).symm
    _ = f T := by rw [← BlackadarKirchberg.matrix_eq_sum_smul_single T]

/-! ## Finite-dimensional domains -/

/-- **Completely positive lifting out of a finite-dimensional C⋆-algebra.**
A nontrivial finite-dimensional `D` is a unital cp retract `D → M_k(ℂ) → D` of
a full matrix algebra; lift `φ ∘ retract` and precompose with the embedding. -/
theorem exists_cp_lift_of_finiteDimensional {D : Type u} {B : Type v} {C : Type w}
    [CStarAlgebra D] [Nontrivial D] [FiniteDimensional ℂ D]
    [CStarAlgebra B] [CStarAlgebra C]
    (π : B →⋆ₐ[ℂ] C) (hπ : Function.Surjective π) {φ : D →ₗ[ℂ] C}
    (hφ : CStarExactness.IsCompletelyPositive φ) :
    ∃ L : D →ₗ[ℂ] B, CStarExactness.IsCompletelyPositive L ∧ ∀ x, π (L x) = φ x := by
  obtain ⟨R⟩ := BlackadarKirchberg.exists_matrixUCPRetract_of_finiteDimensionalCStar D
  obtain ⟨k, ⟨e⟩⟩ : ∃ k : ℕ, Nonempty (R.model ≃ Fin k) := ⟨_, ⟨Fintype.equivFin _⟩⟩
  haveI : Nonempty (Fin k) := ⟨e (Classical.arbitrary R.model)⟩
  let ρ : Matrix R.model R.model ℂ ≃⋆ₐ[ℂ] Matrix (Fin k) (Fin k) ℂ :=
    choiEffrosMatrixReindex e
  let f : Matrix (Fin k) (Fin k) ℂ →ₗ[ℂ] C :=
    φ ∘ₗ R.retract ∘ₗ (ρ.symm.toStarAlgHom.toNonUnitalStarAlgHom :
      Matrix (Fin k) (Fin k) ℂ →ₗ[ℂ] Matrix R.model R.model ℂ)
  have hf : CStarExactness.IsCompletelyPositive f :=
    hφ.comp (R.retract_completelyPositive.comp
      (CStarExactness.isCompletelyPositive_of_starAlgHom
        ρ.symm.toStarAlgHom.toNonUnitalStarAlgHom))
  obtain ⟨L0, hL0, hL0π⟩ := exists_cp_matrix_lift π hπ f hf
  let ι : D →⋆ₐ[ℂ] Matrix (Fin k) (Fin k) ℂ := ρ.toStarAlgHom.comp R.embedding
  refine ⟨L0 ∘ₗ (ι.toNonUnitalStarAlgHom : D →ₗ[ℂ] Matrix (Fin k) (Fin k) ℂ),
    hL0.comp (CStarExactness.isCompletelyPositive_of_starAlgHom ι.toNonUnitalStarAlgHom),
    fun x ↦ ?_⟩
  have hx : f (ι x) = φ x := by
    change φ (R.retract (ρ.symm (ρ (R.embedding x)))) = φ x
    rw [StarAlgEquiv.symm_apply_apply, R.retract_embedding]
  rw [LinearMap.comp_apply]
  exact (hL0π (ι x)).trans hx

/-- **Completely positive contractive lifting out of a finite-dimensional
C⋆-algebra** (Brown–Ozawa, Lemma C.2).  The trivial algebra is handled by the
zero map. -/
theorem exists_cpc_lift_of_finiteDimensional {D : Type u} {B : Type v} {C : Type w}
    [CStarAlgebra D] [FiniteDimensional ℂ D] [CStarAlgebra B] [CStarAlgebra C]
    (π : B →⋆ₐ[ℂ] C) (hπ : Function.Surjective π) {φ : D →ₗ[ℂ] C}
    (hφ : CStarExactness.IsCompletelyPositive φ) (hφc : ∀ x, ‖φ x‖ ≤ ‖x‖) :
    ∃ ψ : D →ₗ[ℂ] B, CStarExactness.IsCompletelyPositive ψ ∧
      (∀ x, ‖ψ x‖ ≤ ‖x‖) ∧ ∀ x, π (ψ x) = φ x := by
  obtain (_ | _) := subsingleton_or_nontrivial D
  · refine ⟨0, BlackadarKirchberg.isCompletelyPositive_zero, fun x ↦ ?_, fun x ↦ ?_⟩
    · rw [LinearMap.zero_apply, norm_zero]
      exact norm_nonneg x
    · rw [LinearMap.zero_apply, map_zero, Subsingleton.elim x 0, map_zero]
  · obtain ⟨L, hL, hLφ⟩ := exists_cp_lift_of_finiteDimensional π hπ hφ
    exact exists_cpc_lift_of_cp_lift π ((hφc 1).trans_eq norm_one) hL hLφ

/-! ## Approximate lifting of nuclear maps -/

/-- **Nuclear maps are approximately liftable.**  If `φ : A → C` is nuclear,
then on every finite set it is approximated in norm by `π ∘ ψ` for a completely
positive contraction `ψ : A → B`: lift the finite-dimensional factor `β` of an
approximate factorization `β ∘ α ≈ φ` (Choi–Effros, proof of Theorem 3.10). -/
theorem exists_cpc_approx_lift_of_isNuclearMap {A : Type u} {B : Type v} {C : Type w}
    [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]
    (π : B →⋆ₐ[ℂ] C) (hπ : Function.Surjective π) {φ : A →ₗ[ℂ] C}
    (hnuc : CStarExactness.IsNuclearMap φ) (F : Finset A) (ε : ℝ) (hε : 0 < ε) :
    ∃ ψ : A →ₗ[ℂ] B, CStarExactness.IsCompletelyPositive ψ ∧
      (∀ a, ‖ψ a‖ ≤ ‖a‖) ∧ ∀ a ∈ F, ‖π (ψ a) - φ a‖ ≤ ε := by
  obtain ⟨D, α, β, hα, hβ, hαc, hβc, happ⟩ := hnuc F ε hε
  obtain ⟨β', hβ', hβ'c, hβ'π⟩ := exists_cpc_lift_of_finiteDimensional π hπ hβ hβc
  refine ⟨β' ∘ₗ α, hβ'.comp hα, fun a ↦ ?_, fun a ha ↦ ?_⟩
  · rw [LinearMap.comp_apply]
    exact (hβ'c (α a)).trans (hαc a)
  · rw [LinearMap.comp_apply, hβ'π]
    exact happ a ha

end

end TWWSchafhauser
end Full
end GroupApproximation
