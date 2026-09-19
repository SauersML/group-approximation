import GroupApproximation.Analysis.ResiduallyFiniteDimensional
import GroupApproximation.Analysis.ShulmanFillNormingProductMF
import GroupApproximation.Analysis.ShulmanFillNormingScalarMF
import Mathlib.Topology.Compactness.Lindelof

/-!
# Separable residually finite-dimensional C-star algebras are MF

This file proves the second assertion in the manuscript sentence

> MF algebras are stably finite, and a separable RFD C-star algebra is MF.

The stable-finiteness assertion is in `MatrixCoronaDedekindFinite`; the RFD
assertion is proved here.  The cozero sets of all finite-dimensional
representations cover the nonzero elements.  A separable metric space is
hereditarily Lindelöf, so a countable subfamily still separates points.  Its
joint representation lands faithfully in a bounded product of matrix
algebras, which is MF by `ShulmanFill.hasMFEmbedding_boundedMatrixSequence`.
-/

namespace GroupApproximation

open scoped Matrix.Norms.L2Operator

noncomputable section

universe u

namespace ResiduallyFiniteDimensionalMF

variable (A : Type u) [CStarAlgebra A]

noncomputable local instance matrixBlockCStarAlgebraForRFD
    (Z : Type*) [Fintype Z] [DecidableEq Z] [Nonempty Z] :
    CStarAlgebra (Matrix Z Z ℂ) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

/-- A finite-dimensional unital star representation, with positivity of its
matrix size recorded so that its matrix model is nonempty. -/
structure Representation where
  dimension : ℕ
  dimension_pos : 0 < dimension
  hom : A →⋆ₐ[ℂ] Matrix (Fin dimension) (Fin dimension) ℂ

/-- The finite matrix model underlying a representation. -/
abbrev Representation.model (r : Representation A) : FiniteModel :=
  ⟨Fin r.dimension, inferInstance, inferInstance⟩

instance Representation.modelNonempty (r : Representation A) :
    Nonempty r.model :=
  Fintype.card_pos_iff.mp (by simpa [Representation.model] using r.dimension_pos)

/-- The set on which a finite-dimensional representation does not vanish. -/
def Representation.cozero (r : Representation A) : Set A :=
  {a | r.hom a ≠ 0}

theorem Representation.isOpen_cozero (r : Representation A) :
    IsOpen r.cozero := by
  have hLipschitz : LipschitzWith 1 r.hom := by
    rw [lipschitzWith_iff_norm_sub_le]
    intro x y
    simpa [map_sub] using
      NonUnitalStarAlgHom.norm_apply_le r.hom.toNonUnitalStarAlgHom (x - y)
  have hpreimage : r.cozero = r.hom ⁻¹' ({0}ᶜ : Set (Matrix
      (Fin r.dimension) (Fin r.dimension) ℂ)) := by
    ext a
    simp [Representation.cozero]
  rw [hpreimage]
  exact isClosed_singleton.isOpen_compl.preimage hLipschitz.continuous

/-- Residual finite-dimensionality supplies at least one positive-dimensional
representation. -/
theorem representation_nonempty [Nontrivial A]
    (hA : IsResiduallyFiniteDimensional A) :
    Nonempty (Representation A) := by
  obtain ⟨n, π, hπ⟩ := hA 1 one_ne_zero
  have hn : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    exact hπ (Subsingleton.elim _ _)
  exact ⟨⟨n, hn, π⟩⟩

/-- In a separable RFD C-star algebra, a sequence of finite-dimensional
representations already separates points. -/
theorem exists_countable_separating_family
    [TopologicalSpace.SeparableSpace A] [Nontrivial A]
    (hA : IsResiduallyFiniteDimensional A) :
    ∃ R : ℕ → Representation A,
      ∀ a : A, a ≠ 0 → ∃ k, (R k).hom a ≠ 0 := by
  letI : Nonempty (Representation A) := representation_nonempty A hA
  have hcover : {a : A | a ≠ 0} ⊆
      ⋃ r : Representation A, r.cozero := by
    intro a ha
    obtain ⟨n, π, hπ⟩ := hA a ha
    have hn : 0 < n := by
      by_contra hn
      have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
      subst n
      exact hπ (Subsingleton.elim _ _)
    exact Set.mem_iUnion.mpr ⟨⟨n, hn, π⟩, hπ⟩
  obtain ⟨R, hR⟩ :=
    (HereditarilyLindelofSpace.isLindelof {a : A | a ≠ 0}).indexed_countable_subcover
      (fun r : Representation A ↦ r.cozero)
      (fun r ↦ r.isOpen_cozero) hcover
  refine ⟨R, fun a ha ↦ ?_⟩
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (hR ha)
  exact ⟨k, hk⟩

variable (R : ℕ → Representation A)

noncomputable local instance boundedMatrixSequenceCStarAlgebraForRFD
    (X : ℕ → Type*) [∀ n, Fintype (X n)] [∀ n, DecidableEq (X n)]
    [∀ n, Nonempty (X n)] : CStarAlgebra (BoundedMatrixSequence X) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

/-- The joint bounded-product representation associated to a sequence of
finite-dimensional representations. -/
def sequenceHom : A →⋆ₐ[ℂ]
    BoundedMatrixSequence (fun k ↦ (R k).model) where
  toFun a := ⟨fun k ↦ (R k).hom a, memℓp_infty ⟨‖a‖, by
    rintro _ ⟨k, rfl⟩
    exact NonUnitalStarAlgHom.norm_apply_le
      (R k).hom.toNonUnitalStarAlgHom a⟩⟩
  map_one' := by apply lp.ext; funext k; exact map_one _
  map_mul' _ _ := by apply lp.ext; funext k; exact map_mul _ _ _
  map_zero' := by apply lp.ext; funext k; exact map_zero _
  map_add' _ _ := by apply lp.ext; funext k; exact map_add _ _ _
  commutes' _ := by apply lp.ext; funext k; exact (R k).hom.commutes _
  map_star' _ := by apply lp.ext; funext k; exact map_star _ _

@[simp] theorem sequenceHom_apply (a : A) (k : ℕ) :
    sequenceHom A R a k = (R k).hom a :=
  rfl

theorem sequenceHom_injective
    (hR : ∀ a : A, a ≠ 0 → ∃ k, (R k).hom a ≠ 0) :
    Function.Injective (sequenceHom A R) := by
  intro a b hab
  by_contra hne
  obtain ⟨k, hk⟩ := hR (a - b) (sub_ne_zero.mpr hne)
  have hcoord := congrArg
    (fun x : BoundedMatrixSequence (fun k ↦ (R k).model) ↦ x k) hab
  exact hk (by simpa only [sequenceHom_apply, map_sub, sub_eq_zero] using hcoord)

/-- **A separable residually finite-dimensional C-star algebra is MF.** -/
theorem isMFAlgebra [TopologicalSpace.SeparableSpace A]
    (hA : IsResiduallyFiniteDimensional A) : IsMFAlgebra A := by
  rcases subsingleton_or_nontrivial A with hsub | hnontrivial
  · letI : Subsingleton A := hsub
    let z : A →⋆ₙₐ[ℂ] ℂ := 0
    refine ⟨inferInstance, HasMFEmbedding.of_injective_nonUnitalStarAlgHom
      ShulmanFill.hasMFEmbedding_complex z ?_⟩
    intro a b _
    exact Subsingleton.elim a b
  · letI : Nontrivial A := hnontrivial
    obtain ⟨R, hR⟩ := exists_countable_separating_family A hA
    refine ⟨inferInstance, ?_⟩
    exact HasMFEmbedding.of_injective_nonUnitalStarAlgHom
      (ShulmanFill.hasMFEmbedding_boundedMatrixSequence
        (fun k ↦ (R k).model))
      (sequenceHom A R).toNonUnitalStarAlgHom
      (sequenceHom_injective A R hR)

end ResiduallyFiniteDimensionalMF

end

end GroupApproximation

#print axioms GroupApproximation.ResiduallyFiniteDimensionalMF.isMFAlgebra
