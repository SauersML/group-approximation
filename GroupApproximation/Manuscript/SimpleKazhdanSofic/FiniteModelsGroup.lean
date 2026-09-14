import GroupApproximation.Pestov91.LEF
import GroupApproximation.Pestov91.LEFHyperlinear
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Data.Matrix.Composition

/-!
# `simple_kazhdan_sofic_group.tex`, "Finite models": from ring models to group models

`simple_kazhdan_sofic_group.tex` at bf961c128, tex 146–152:

> For a finite subset of $G$, include the entries of its elements, their inverses, their
> differences, and all intermediate sums and products needed for matrix multiplication. The
> resulting model is an injective partial homomorphism into $\GL_{3N}(\F_2)$. Thus $G$ is LEF.
> The regular permutation actions of these finite groups give sofic models; their permutation
> matrices give hyperlinear models~\cite{Pestov}.

The ring models of tex 131–145 send a finite part of `R` into a full matrix algebra `M_N(F₂)`.
This module takes such models as the hypothesis `IsMatricialLEFRing K A` (over any ring `K`) and
proves the printed steps:

* `IsMatricialLEFRing.matrix`: entrywise, including all intermediate sums and products of matrix
  multiplication, a matricial ring model of `A` gives one of `M_n(A)` into `M_{n × N}(K)`
  (`Matrix.compRingEquiv`);
* `exists_units_model`: a ring model on a table containing `u` and `u⁻¹` gives an injective
  partial group homomorphism of units;
* `IsMatricialLEFRing.exists_generalLinear_model`: every finite subset of `GL_n(A)` has an injective
  partial homomorphism into `GL_{n × N}(K)`, the printed `GL_{3N}(F₂)` for `n = 3`, `K = F₂`;
* `IsMatricialLEFRing.isLEF_elementaryGroup`: "Thus $G$ is LEF";
* sofic and hyperlinear models: `isSofic_of_isLEF` (left regular representations of the finite
  models) and `Pestov91.isHyperlinear_of_isLEF` (their permutation matrices);
* closed endpoints `printedFiniteModelsGeneralLinear` and `printedFiniteModelsLEFSoficHyperlinear`.

The differences named in the printed sentence are not needed for the Lean model: injectivity on
the table of entries already separates distinct matrices.
-/

namespace GroupApproximation

namespace SimpleKazhdanSofic

open Pestov91

/-- Finite ring models into full matrix algebras over `K` (the models of tex 131–145 over `F₂`):
every finite `t ⊆ A` admits `φ : A → M_N(K)`, injective on `t`, with `φ 0 = 0` and `φ 1 = 1`, and
preserving the sums and products of pairs from `t`. -/
def IsMatricialLEFRing (K : Type*) [Ring K] (A : Type*) [Ring A] : Prop :=
  ∀ t : Finset A, ∃ (N : ℕ) (φ : A → Matrix (Fin N) (Fin N) K),
    Set.InjOn φ (t : Set A) ∧ φ 0 = 0 ∧ φ 1 = 1 ∧
      ∀ a ∈ t, ∀ b ∈ t, φ (a + b) = φ a + φ b ∧ φ (a * b) = φ a * φ b

/-- Matricial finite models over a finite ring are finite ring models: `A` is LEF. -/
theorem IsMatricialLEFRing.isLEFRing {K A : Type} [Ring K] [Finite K] [Ring A]
    (hA : IsMatricialLEFRing K A) : IsLEFRing A := fun t => by
  obtain ⟨N, φ, hinj, h0, h1, hφ⟩ := hA t
  exact ⟨Matrix (Fin N) (Fin N) K, inferInstance,
    inferInstanceAs (Finite (Fin N → Fin N → K)), φ, hinj, h0, h1, hφ⟩

/-- "For a finite subset of $G$, include the entries of its elements ... and all intermediate sums
and products needed for matrix multiplication" (tex 146–148): entrywise, a matricial ring model of
`A` gives a ring model of `M_n(A)` into `M_{n × N}(K)`. -/
theorem IsMatricialLEFRing.matrix {K A : Type} [Ring K] [Ring A] (hA : IsMatricialLEFRing K A)
    (n : ℕ) (t : Finset (Matrix (Fin n) (Fin n) A)) :
    ∃ (N : ℕ) (ψ : Matrix (Fin n) (Fin n) A → Matrix (Fin n × Fin N) (Fin n × Fin N) K),
      Set.InjOn ψ (t : Set (Matrix (Fin n) (Fin n) A)) ∧ ψ 0 = 0 ∧ ψ 1 = 1 ∧
        ∀ M ∈ t, ∀ M' ∈ t, ψ (M + M') = ψ M + ψ M' ∧ ψ (M * M') = ψ M * ψ M' := by
  classical
  obtain ⟨t', hE, hP⟩ : ∃ t' : Finset A, (∀ M ∈ t, ∀ i j, M i j ∈ t') ∧
      ∀ M ∈ t, ∀ M' ∈ t, ∀ i j, ∀ S : Finset (Fin n), ∑ k ∈ S, M i k * M' k j ∈ t' := by
    refine ⟨(t ×ˢ (Finset.univ : Finset (Fin n × Fin n))).image (fun q ↦ q.1 q.2.1 q.2.2) ∪
      (t ×ˢ t ×ˢ (Finset.univ : Finset (Fin n × Fin n)) ×ˢ
          (Finset.univ : Finset (Finset (Fin n)))).image
        (fun q ↦ ∑ k ∈ q.2.2.2, q.1 q.2.2.1.1 k * q.2.1 k q.2.2.1.2), ?_, ?_⟩
    · intro M hM i j
      exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨(M, (i, j)), by simp [hM], rfl⟩)
    · intro M hM M' hM' i j S
      exact Finset.mem_union_right _
        (Finset.mem_image.2 ⟨(M, M', (i, j), S), by simp [hM, hM'], rfl⟩)
  obtain ⟨N, φ, hinj, h0, h1, hφ⟩ := hA t'
  have hsum : ∀ M ∈ t, ∀ M' ∈ t, ∀ i j, ∀ S : Finset (Fin n),
      φ (∑ k ∈ S, M i k * M' k j) = ∑ k ∈ S, φ (M i k) * φ (M' k j) := by
    intro M hM M' hM' i j S
    refine Finset.induction_on S (by simpa using h0) ?_
    intro a S ha ih
    have hprod : M i a * M' a j ∈ t' := by simpa using hP M hM M' hM' i j {a}
    rw [Finset.sum_insert ha, Finset.sum_insert ha, (hφ _ hprod _ (hP M hM M' hM' i j S)).1, ih,
      (hφ _ (hE M hM i a) _ (hE M' hM' a j)).2]
  refine ⟨N, fun M ↦ Matrix.compRingEquiv (Fin n) (Fin N) K (M.map φ), ?_, ?_, ?_, ?_⟩
  · intro M hM M' hM' hMM'
    have h : M.map φ = M'.map φ := (Matrix.compRingEquiv (Fin n) (Fin N) K).injective hMM'
    exact Matrix.ext fun i j => hinj (hE M hM i j) (hE M' hM' i j) (congrFun (congrFun h i) j)
  · show Matrix.compRingEquiv (Fin n) (Fin N) K ((0 : Matrix (Fin n) (Fin n) A).map φ) = 0
    rw [Matrix.map_zero φ h0, map_zero]
  · show Matrix.compRingEquiv (Fin n) (Fin N) K ((1 : Matrix (Fin n) (Fin n) A).map φ) = 1
    rw [Matrix.map_one φ h0 h1, map_one]
  · intro M hM M' hM'
    refine ⟨?_, ?_⟩
    · show Matrix.compRingEquiv (Fin n) (Fin N) K ((M + M').map φ) =
        Matrix.compRingEquiv (Fin n) (Fin N) K (M.map φ) +
          Matrix.compRingEquiv (Fin n) (Fin N) K (M'.map φ)
      rw [← map_add]
      congr 1
      exact Matrix.ext fun i j => (hφ _ (hE M hM i j) _ (hE M' hM' i j)).1
    · show Matrix.compRingEquiv (Fin n) (Fin N) K ((M * M').map φ) =
        Matrix.compRingEquiv (Fin n) (Fin N) K (M.map φ) *
          Matrix.compRingEquiv (Fin n) (Fin N) K (M'.map φ)
      rw [← map_mul]
      congr 1
      refine Matrix.ext fun i j => ?_
      simp only [Matrix.map_apply, Matrix.mul_apply]
      exact hsum M hM M' hM' i j Finset.univ

/-- "... their inverses ..." (tex 147): a ring model on a table containing `u` and `u⁻¹` for every
`u ∈ s` gives an injective partial group homomorphism `Aˣ → Fˣ` on `s`. -/
theorem exists_units_model {A F : Type*} [Ring A] [Ring F] (s : Finset Aˣ) (t : Finset A)
    (hv : ∀ u ∈ s, (u : A) ∈ t) (hi : ∀ u ∈ s, ((u⁻¹ : Aˣ) : A) ∈ t) (φ : A → F)
    (hinj : Set.InjOn φ (t : Set A)) (h1 : φ 1 = 1)
    (hφ : ∀ a ∈ t, ∀ b ∈ t, φ (a + b) = φ a + φ b ∧ φ (a * b) = φ a * φ b) :
    ∃ g : Aˣ → Fˣ, Set.InjOn g (s : Set Aˣ) ∧ ∀ u ∈ s, ∀ v ∈ s, g (u * v) = g u * g v := by
  classical
  have hunit : ∀ u ∈ s, φ u * φ ((u⁻¹ : Aˣ) : A) = 1 ∧ φ ((u⁻¹ : Aˣ) : A) * φ u = 1 :=
    fun u hu ↦ ⟨by rw [← (hφ _ (hv u hu) _ (hi u hu)).2, Units.mul_inv, h1],
      by rw [← (hφ _ (hi u hu) _ (hv u hu)).2, Units.inv_mul, h1]⟩
  obtain ⟨g, hg⟩ : ∃ g : Aˣ → Fˣ, ∀ (u : Aˣ) (_ : φ u * φ ((u⁻¹ : Aˣ) : A) = 1 ∧
      φ ((u⁻¹ : Aˣ) : A) * φ u = 1), (g u : F) = φ u :=
    ⟨fun u ↦ if h : φ u * φ ((u⁻¹ : Aˣ) : A) = 1 ∧ φ ((u⁻¹ : Aˣ) : A) * φ u = 1 then
      ⟨φ u, φ ((u⁻¹ : Aˣ) : A), h.1, h.2⟩ else 1,
      fun u h ↦ by simp only [dif_pos h]⟩
  refine ⟨g, ?_, ?_⟩
  · intro u hu v hv' huv
    exact Units.ext (hinj (hv u hu) (hv v hv') (by
      rw [← hg u (hunit u hu), ← hg v (hunit v hv'), huv]))
  · intro u hu v hv'
    have hmul : φ ((u * v : Aˣ) : A) = φ u * φ v := by
      rw [Units.val_mul]
      exact (hφ _ (hv u hu) _ (hv v hv')).2
    have hinv : φ (((u * v)⁻¹ : Aˣ) : A) = φ ((v⁻¹ : Aˣ) : A) * φ ((u⁻¹ : Aˣ) : A) := by
      rw [mul_inv_rev, Units.val_mul]
      exact (hφ _ (hi v hv') _ (hi u hu)).2
    have huv : φ ((u * v : Aˣ) : A) * φ (((u * v)⁻¹ : Aˣ) : A) = 1 ∧
        φ (((u * v)⁻¹ : Aˣ) : A) * φ ((u * v : Aˣ) : A) = 1 := by
      rw [hmul, hinv]
      refine ⟨?_, ?_⟩
      · calc φ u * φ v * (φ ((v⁻¹ : Aˣ) : A) * φ ((u⁻¹ : Aˣ) : A))
            = φ u * (φ v * φ ((v⁻¹ : Aˣ) : A)) * φ ((u⁻¹ : Aˣ) : A) := by
              simp only [mul_assoc]
          _ = 1 := by rw [(hunit v hv').1, mul_one, (hunit u hu).1]
      · calc φ ((v⁻¹ : Aˣ) : A) * φ ((u⁻¹ : Aˣ) : A) * (φ u * φ v)
            = φ ((v⁻¹ : Aˣ) : A) * (φ ((u⁻¹ : Aˣ) : A) * φ u) * φ v := by
              simp only [mul_assoc]
          _ = 1 := by rw [(hunit u hu).2, mul_one, (hunit v hv').2]
    exact Units.ext (by
      rw [Units.val_mul, hg _ huv, hg u (hunit u hu), hg v (hunit v hv'), hmul])

/-- "The resulting model is an injective partial homomorphism into $\GL_{3N}(\F_2)$" (tex
148–149): every finite subset of `GL_n(A)` has an injective partial homomorphism into
`GL_{n × N}(K)`. -/
theorem IsMatricialLEFRing.exists_generalLinear_model {K A : Type} [Ring K] [Ring A]
    (hA : IsMatricialLEFRing K A) (n : ℕ) (s : Finset (Matrix (Fin n) (Fin n) A)ˣ) :
    ∃ (N : ℕ) (g : (Matrix (Fin n) (Fin n) A)ˣ → (Matrix (Fin n × Fin N) (Fin n × Fin N) K)ˣ),
      Set.InjOn g (s : Set (Matrix (Fin n) (Fin n) A)ˣ) ∧
        ∀ u ∈ s, ∀ v ∈ s, g (u * v) = g u * g v := by
  classical
  obtain ⟨t, hv, hi⟩ : ∃ t : Finset (Matrix (Fin n) (Fin n) A),
      (∀ u ∈ s, (u : Matrix (Fin n) (Fin n) A) ∈ t) ∧
        ∀ u ∈ s, ((u⁻¹ : (Matrix (Fin n) (Fin n) A)ˣ) : Matrix (Fin n) (Fin n) A) ∈ t :=
    ⟨s.image (fun u : (Matrix (Fin n) (Fin n) A)ˣ ↦ (u : Matrix (Fin n) (Fin n) A)) ∪
        s.image (fun u : (Matrix (Fin n) (Fin n) A)ˣ ↦
          ((u⁻¹ : (Matrix (Fin n) (Fin n) A)ˣ) : Matrix (Fin n) (Fin n) A)),
      fun u hu ↦ Finset.mem_union_left _ (Finset.mem_image_of_mem _ hu),
      fun u hu ↦ Finset.mem_union_right _ (Finset.mem_image_of_mem _ hu)⟩
  obtain ⟨N, ψ, hinj, -, h1, hψ⟩ := hA.matrix n t
  exact ⟨N, exists_units_model s t hv hi ψ hinj h1 hψ⟩

/-- "Thus $G$ is LEF" (tex 149): `EL_n(A)` is LEF when `A` has matricial finite models over a finite
ring `K`, through the partial homomorphisms into `GL_{n × N}(K)`. -/
theorem IsMatricialLEFRing.isLEF_elementaryGroup {K A : Type} [Ring K] [Finite K] [Ring A]
    (hA : IsMatricialLEFRing K A) (n : ℕ) : IsLEF ↥(elementaryGroup (Fin n) A) :=
  isLEF_of_injective (elementaryGroup (Fin n) A).subtype Subtype.val_injective
    (isLEF_of_forall_finite_model fun s => by
      obtain ⟨N, g, hinj, hmul⟩ := hA.exists_generalLinear_model n s
      haveI : Finite (Matrix (Fin n × Fin N) (Fin n × Fin N) K) :=
        inferInstanceAs (Finite (Fin n × Fin N → Fin n × Fin N → K))
      exact ⟨(Matrix (Fin n × Fin N) (Fin n × Fin N) K)ˣ, inferInstance, inferInstance, g, hinj,
        hmul⟩)

/-- **tex 146–149**, the printed finite models of `G = EL_3(R)`: a ring with matricial finite models
over `K` has, for every finite subset of `GL_3(R)`, an injective partial homomorphism into
`GL_{3 × N}(K)`, the printed `GL_{3N}(F₂)`. -/
def PrintedFiniteModelsGeneralLinear : Prop :=
  ∀ (K A : Type) [Ring K] [Ring A], IsMatricialLEFRing K A →
    ∀ s : Finset (Matrix (Fin 3) (Fin 3) A)ˣ, ∃ (N : ℕ)
      (g : (Matrix (Fin 3) (Fin 3) A)ˣ → (Matrix (Fin 3 × Fin N) (Fin 3 × Fin N) K)ˣ),
      Set.InjOn g (s : Set (Matrix (Fin 3) (Fin 3) A)ˣ) ∧
        ∀ u ∈ s, ∀ v ∈ s, g (u * v) = g u * g v

theorem printedFiniteModelsGeneralLinear : PrintedFiniteModelsGeneralLinear :=
  fun _ _ _ _ hA s => hA.exists_generalLinear_model 3 s

/-- **tex 149–152**, "Thus $G$ is LEF.  The regular permutation actions of these finite groups give
sofic models; their permutation matrices give hyperlinear models": for a ring with matricial finite
models over a finite ring, `EL_3` is LEF, sofic and hyperlinear. -/
def PrintedFiniteModelsLEFSoficHyperlinear : Prop :=
  ∀ (K A : Type) [Ring K] [Finite K] [Ring A], IsMatricialLEFRing K A →
    IsLEF ↥(elementaryGroup (Fin 3) A) ∧ IsSofic ↥(elementaryGroup (Fin 3) A) ∧
      IsHyperlinear ↥(elementaryGroup (Fin 3) A)

theorem printedFiniteModelsLEFSoficHyperlinear : PrintedFiniteModelsLEFSoficHyperlinear :=
  fun _ _ _ _ _ hA => ⟨hA.isLEF_elementaryGroup 3, isSofic_of_isLEF (hA.isLEF_elementaryGroup 3),
    isHyperlinear_of_isLEF (hA.isLEF_elementaryGroup 3)⟩

end SimpleKazhdanSofic

end GroupApproximation

#audit_axioms GroupApproximation.SimpleKazhdanSofic.IsMatricialLEFRing.isLEFRing
#audit_axioms GroupApproximation.SimpleKazhdanSofic.IsMatricialLEFRing.matrix
#audit_axioms GroupApproximation.SimpleKazhdanSofic.exists_units_model
#audit_axioms GroupApproximation.SimpleKazhdanSofic.IsMatricialLEFRing.exists_generalLinear_model
#audit_axioms GroupApproximation.SimpleKazhdanSofic.IsMatricialLEFRing.isLEF_elementaryGroup
#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedFiniteModelsGeneralLinear
#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedFiniteModelsLEFSoficHyperlinear
