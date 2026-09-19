import GroupApproximation.Analysis.FiniteMatrixAbstractInvolutionCorrection

/-!
# Correcting an Artin--Wedderburn product equivalence to preserve star

An algebraic Wedderburn equivalence transports the C-star involution to a
finite product of matrix blocks.  Central coordinate idempotents are fixed,
so the transported involution preserves every block.  Each restriction has
the abstract full-matrix involution properties isolated in
`FiniteMatrixAbstractInvolutionCorrection`; correcting the blocks and taking
their finite product gives a star-algebra equivalence.
-/

namespace GroupApproximation
namespace BlackadarKirchberg

open scoped Matrix.Norms.L2Operator

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]
variable (d : I → ℕ) [∀ i, Nonempty (Fin (d i))]

local instance matrixBlockCStarAlgebraForProductCorrection (i : I) :
    CStarAlgebra (Matrix (Fin (d i)) (Fin (d i)) ℂ) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

local instance directMatrixSumCStarAlgebraForProductCorrection :
    CStarAlgebra (DirectMatrixSum d) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

local instance boundedMatrixSequenceCStarAlgebraForProductCorrection
    (X : ℕ → Type*) [∀ n, Fintype (X n)] [∀ n, DecidableEq (X n)]
    [∀ n, Nonempty (X n)] : CStarAlgebra (BoundedMatrixSequence X) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

/-- Insert one matrix into a coordinate of the dependent matrix product. -/
def blockSingle (i : I) (x : Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    DirectMatrixSum d :=
  Pi.single (M := fun j : I ↦ Matrix (Fin (d j)) (Fin (d j)) ℂ) i x

omit [Fintype I] [∀ i, Nonempty (Fin (d i))] in
@[simp] theorem blockSingle_apply_same (i : I)
    (x : Matrix (Fin (d i)) (Fin (d i)) ℂ) : blockSingle d i x i = x := by
  simp [blockSingle]

omit [Fintype I] [∀ i, Nonempty (Fin (d i))] in
@[simp] theorem blockSingle_apply_of_ne {i j : I} (h : j ≠ i)
    (x : Matrix (Fin (d i)) (Fin (d i)) ℂ) : blockSingle d i x j = 0 := by
  simp [blockSingle, h]

/-- The identity of one coordinate, extended by zero to the finite product. -/
def coordinateIdempotent (i : I) : DirectMatrixSum d := blockSingle d i 1

omit [Fintype I] [∀ i, Nonempty (Fin (d i))] in
theorem coordinateIdempotent_apply_same (i : I) :
    coordinateIdempotent d i i = 1 := by simp [coordinateIdempotent]

omit [Fintype I] [∀ i, Nonempty (Fin (d i))] in
theorem coordinateIdempotent_apply_of_ne {i j : I} (h : j ≠ i) :
    coordinateIdempotent d i j = 0 := by simp [coordinateIdempotent, h]

omit [Fintype I] [∀ i, Nonempty (Fin (d i))] in
/-- A coordinate identity is a central idempotent of the matrix product. -/
theorem coordinateIdempotent_mem_center (i : I) :
    coordinateIdempotent d i ∈ Subring.center (DirectMatrixSum d) := by
  rw [Subring.mem_center_iff]
  intro x
  funext j
  by_cases h : j = i
  · subst j
    simp [coordinateIdempotent]
  · simp [coordinateIdempotent, h]

omit [Fintype I] [∀ i, Nonempty (Fin (d i))] in
theorem coordinateIdempotent_isIdempotentElem (i : I) :
    IsIdempotentElem (coordinateIdempotent d i) := by
  funext j
  by_cases h : j = i
  · subst j
    simp [coordinateIdempotent]
  · simp [coordinateIdempotent, h]

omit [Fintype I] [∀ i, Nonempty (Fin (d i))] in
/-- The involution transported by a Wedderburn equivalence fixes every
coordinate identity. -/
theorem transportedInvolution_coordinateIdempotent
    {D : Type*} [CStarAlgebra D] (e : D ≃ₐ[ℂ] DirectMatrixSum d)
    (i : I) :
    transportedInvolution e (coordinateIdempotent d i) =
      coordinateIdempotent d i :=
  algEquiv_transport_star_fixes_central_idempotent e
    (coordinateIdempotent_mem_center d i)
    (coordinateIdempotent_isIdempotentElem d i)

/-- Restriction of the transported involution to one matrix block. -/
def blockTransportedInvolution
    {D : Type*} [CStarAlgebra D] (e : D ≃ₐ[ℂ] DirectMatrixSum d)
    (i : I) (x : Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    Matrix (Fin (d i)) (Fin (d i)) ℂ :=
  transportedInvolution e (blockSingle d i x) i

omit [Fintype I] [∀ i, Nonempty (Fin (d i))] in
/-- The transported involution of a block-supported element remains
block-supported. -/
theorem transportedInvolution_single
    {D : Type*} [CStarAlgebra D] (e : D ≃ₐ[ℂ] DirectMatrixSum d)
    (i : I) (x : Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    transportedInvolution e (blockSingle d i x) =
      blockSingle d i (blockTransportedInvolution d e i x) := by
  have hsingle : blockSingle d i x =
      coordinateIdempotent d i * blockSingle d i x := by
    funext j
    by_cases h : j = i
    · subst j
      simp [coordinateIdempotent]
    · simp [coordinateIdempotent, h]
  have hsupp : transportedInvolution e (blockSingle d i x) =
      transportedInvolution e (blockSingle d i x) * coordinateIdempotent d i := by
    calc
      transportedInvolution e (blockSingle d i x) =
          transportedInvolution e
            (coordinateIdempotent d i * blockSingle d i x) := congrArg _ hsingle
      _ = transportedInvolution e (blockSingle d i x) *
          transportedInvolution e (coordinateIdempotent d i) :=
            transportedInvolution_mul e (coordinateIdempotent d i)
              (blockSingle d i x)
      _ = transportedInvolution e (blockSingle d i x) * coordinateIdempotent d i := by
            rw [transportedInvolution_coordinateIdempotent]
  funext j
  by_cases h : j = i
  · subst j
    simp [blockSingle, blockTransportedInvolution]
  · have hj := congrFun hsupp j
    simpa [coordinateIdempotent, h] using hj

omit [Fintype I] [∀ i, Nonempty (Fin (d i))] in
/-- Every coordinate of the global transported involution is obtained by
applying the corresponding restricted block involution. -/
theorem transportedInvolution_apply
    {D : Type*} [CStarAlgebra D] (e : D ≃ₐ[ℂ] DirectMatrixSum d)
    (x : DirectMatrixSum d) (i : I) :
    transportedInvolution e x i = blockTransportedInvolution d e i (x i) := by
  have hsingle : blockSingle d i (x i) = coordinateIdempotent d i * x := by
    funext j
    by_cases h : j = i
    · subst j
      simp [coordinateIdempotent]
    · simp [coordinateIdempotent, h]
  calc
    transportedInvolution e x i =
        (transportedInvolution e x * coordinateIdempotent d i) i := by
          simp [coordinateIdempotent]
    _ = transportedInvolution e (coordinateIdempotent d i * x) i := by
          rw [transportedInvolution_mul,
            transportedInvolution_coordinateIdempotent]
    _ = transportedInvolution e (blockSingle d i (x i)) i := by rw [hsingle]
    _ = blockTransportedInvolution d e i (x i) := rfl

omit [Fintype I] [∀ i, Nonempty (Fin (d i))] in
theorem blockTransportedInvolution_zero
    {D : Type*} [CStarAlgebra D] (e : D ≃ₐ[ℂ] DirectMatrixSum d)
    (i : I) : blockTransportedInvolution d e i 0 = 0 := by
  have hz : blockSingle d i 0 = 0 := by
    funext j
    by_cases h : j = i
    · subst j
      simp
    · simp [h]
  rw [blockTransportedInvolution, hz, transportedInvolution_zero]
  rfl

omit [Fintype I] [∀ i, Nonempty (Fin (d i))] in
theorem blockTransportedInvolution_one
    {D : Type*} [CStarAlgebra D] (e : D ≃ₐ[ℂ] DirectMatrixSum d)
    (i : I) : blockTransportedInvolution d e i 1 = 1 := by
  change transportedInvolution e (coordinateIdempotent d i) i = 1
  rw [transportedInvolution_coordinateIdempotent]
  simp [coordinateIdempotent]

omit [Fintype I] [∀ i, Nonempty (Fin (d i))] in
theorem blockTransportedInvolution_add
    {D : Type*} [CStarAlgebra D] (e : D ≃ₐ[ℂ] DirectMatrixSum d)
    (i : I) (x y : Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    blockTransportedInvolution d e i (x + y) =
      blockTransportedInvolution d e i x +
        blockTransportedInvolution d e i y := by
  have hadd : blockSingle d i (x + y) =
      blockSingle d i x + blockSingle d i y := by
    funext j
    by_cases h : j = i
    · subst j
      simp
    · simp [h]
  calc
    transportedInvolution e (blockSingle d i (x + y)) i =
        transportedInvolution e (blockSingle d i x + blockSingle d i y) i :=
          congrArg (fun z ↦ transportedInvolution e z i) hadd
    _ = blockTransportedInvolution d e i x +
        blockTransportedInvolution d e i y := by
          rw [transportedInvolution_add]
          rfl

omit [Fintype I] [∀ i, Nonempty (Fin (d i))] in
theorem blockTransportedInvolution_mul
    {D : Type*} [CStarAlgebra D] (e : D ≃ₐ[ℂ] DirectMatrixSum d)
    (i : I) (x y : Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    blockTransportedInvolution d e i (x * y) =
      blockTransportedInvolution d e i y *
        blockTransportedInvolution d e i x := by
  have hmul : blockSingle d i (x * y) =
      blockSingle d i x * blockSingle d i y := by
    funext j
    by_cases h : j = i
    · subst j
      simp
    · simp [h]
  calc
    transportedInvolution e (blockSingle d i (x * y)) i =
        transportedInvolution e (blockSingle d i x * blockSingle d i y) i :=
          congrArg (fun z ↦ transportedInvolution e z i) hmul
    _ = blockTransportedInvolution d e i y *
        blockTransportedInvolution d e i x := by
          rw [transportedInvolution_mul]
          rfl

omit [Fintype I] [∀ i, Nonempty (Fin (d i))] in
theorem blockTransportedInvolution_smul
    {D : Type*} [CStarAlgebra D] (e : D ≃ₐ[ℂ] DirectMatrixSum d)
    (i : I) (c : ℂ) (x : Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    blockTransportedInvolution d e i (c • x) =
      star c • blockTransportedInvolution d e i x := by
  have hsmul : blockSingle d i (c • x) = c • blockSingle d i x := by
    funext j
    by_cases h : j = i
    · subst j
      simp
    · simp [h]
  calc
    transportedInvolution e (blockSingle d i (c • x)) i =
        transportedInvolution e (c • blockSingle d i x) i :=
          congrArg (fun z ↦ transportedInvolution e z i) hsmul
    _ = star c • blockTransportedInvolution d e i x := by
          rw [transportedInvolution_smul]
          rfl

omit [Fintype I] [∀ i, Nonempty (Fin (d i))] in
theorem blockTransportedInvolution_involutive
    {D : Type*} [CStarAlgebra D] (e : D ≃ₐ[ℂ] DirectMatrixSum d)
    (i : I) (x : Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    blockTransportedInvolution d e i
      (blockTransportedInvolution d e i x) = x := by
  have h := congrFun (congrArg (transportedInvolution e)
    (transportedInvolution_single d e i x)) i
  rw [transportedInvolution_involutive] at h
  simpa [blockTransportedInvolution] using h.symm

omit [Fintype I] [∀ i, Nonempty (Fin (d i))] in
theorem blockTransportedInvolution_gram_eq_zero_iff
    {D : Type*} [CStarAlgebra D] (e : D ≃ₐ[ℂ] DirectMatrixSum d)
    (i : I) (x : Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    blockTransportedInvolution d e i x * x = 0 ↔ x = 0 := by
  constructor
  · intro hzero
    have hglobal : transportedInvolution e (blockSingle d i x) *
        blockSingle d i x = 0 := by
      rw [transportedInvolution_single]
      funext j
      by_cases h : j = i
      · subst j
        simpa using hzero
      · simp [h]
    have hsingleZero := (transportedInvolution_mul_self_eq_zero_iff e
      (blockSingle d i x)).mp hglobal
    have hi := congrFun hsingleZero i
    simpa using hi
  · rintro rfl
    simp [blockTransportedInvolution_zero]

/-! ## Transfer to endomorphisms and correction of one block -/

/-- The standard star-equivalence from a matrix block to algebraic
endomorphisms of its Euclidean space. -/
def matrixToModuleEndStarAlgEquiv (i : I) :
    Matrix (Fin (d i)) (Fin (d i)) ℂ ≃⋆ₐ[ℂ]
      Module.End ℂ (EuclideanSpace ℂ (Fin (d i))) :=
  (Matrix.toEuclideanCLM (n := Fin (d i)) (𝕜 := ℂ)).trans
    (moduleEndToContinuousStarAlgEquiv
      (EuclideanSpace ℂ (Fin (d i)))).symm

/-- The restricted transported involution, moved to algebraic
endomorphisms, has all properties needed by the abstract correction theorem. -/
def blockFullMatrixInvolutionData
    {D : Type*} [CStarAlgebra D] (e : D ≃ₐ[ℂ] DirectMatrixSum d)
    (i : I) :
    FullMatrixInvolutionData (EuclideanSpace ℂ (Fin (d i))) where
  tau A := matrixToModuleEndStarAlgEquiv d i
    (blockTransportedInvolution d e i
      ((matrixToModuleEndStarAlgEquiv d i).symm A))
  map_zero := by simp [blockTransportedInvolution_zero]
  map_one := by simp [blockTransportedInvolution_one]
  map_add x y := by simp [blockTransportedInvolution_add]
  map_mul x y := by simp [blockTransportedInvolution_mul]
  map_smul c x := by simp [blockTransportedInvolution_smul]
  involutive x := by simp [blockTransportedInvolution_involutive]
  gram_eq_zero_iff x := by
    constructor
    · intro hzero
      have hsource :
          blockTransportedInvolution d e i
              ((matrixToModuleEndStarAlgEquiv d i).symm x) *
            (matrixToModuleEndStarAlgEquiv d i).symm x = 0 := by
        let m := matrixToModuleEndStarAlgEquiv d i
        apply m.injective
        calc
          m (blockTransportedInvolution d e i (m.symm x) * m.symm x) =
              m (blockTransportedInvolution d e i (m.symm x)) *
                m (m.symm x) := map_mul m _ _
          _ = m (blockTransportedInvolution d e i (m.symm x)) * x := by
                rw [m.apply_symm_apply]
          _ = 0 := hzero
          _ = m 0 := (map_zero m).symm
      have hxsource :=
        (blockTransportedInvolution_gram_eq_zero_iff d e i _).mp hsource
      apply (matrixToModuleEndStarAlgEquiv d i).symm.injective
      simpa using hxsource
    · rintro rfl
      simp [blockTransportedInvolution_zero]

omit [Fintype I] in
/-- Each block admits an algebra automorphism intertwining its restricted
transported involution with the ordinary matrix adjoint. -/
theorem exists_blockIntertwiningAlgEquiv
    {D : Type*} [CStarAlgebra D] (e : D ≃ₐ[ℂ] DirectMatrixSum d)
    (i : I) :
    ∃ c : Matrix (Fin (d i)) (Fin (d i)) ℂ ≃ₐ[ℂ]
        Matrix (Fin (d i)) (Fin (d i)) ℂ,
      ∀ x, c (blockTransportedInvolution d e i x) = star (c x) := by
  let m := matrixToModuleEndStarAlgEquiv d i
  obtain ⟨cEnd, hcEnd⟩ :=
    (blockFullMatrixInvolutionData d e i).exists_intertwiningAlgEquiv
  let c : Matrix (Fin (d i)) (Fin (d i)) ℂ ≃ₐ[ℂ]
      Matrix (Fin (d i)) (Fin (d i)) ℂ :=
    m.toAlgEquiv |>.trans (cEnd.trans m.symm.toAlgEquiv)
  refine ⟨c, ?_⟩
  intro x
  change m.symm (cEnd (m (blockTransportedInvolution d e i x))) =
    star (m.symm (cEnd (m x)))
  apply m.injective
  have hc := hcEnd (m x)
  change cEnd
      (m (blockTransportedInvolution d e i (m.symm (m x)))) =
        star (cEnd (m x)) at hc
  rw [m.symm_apply_apply] at hc
  calc
    m (m.symm (cEnd (m (blockTransportedInvolution d e i x)))) =
        cEnd (m (blockTransportedInvolution d e i x)) := m.apply_symm_apply _
    _ = star (cEnd (m x)) := hc
    _ = m (star (m.symm (cEnd (m x)))) := by
      rw [map_star, m.apply_symm_apply]

/-! ## Product gluing -/

omit [Fintype I] in
/-- Every algebraic Wedderburn equivalence from a C-star algebra to a finite
product of nonzero full matrix algebras can be corrected blockwise to a
star-algebra equivalence. -/
theorem exists_correctedStarAlgEquiv_to_directMatrixSum
    {D : Type*} [CStarAlgebra D] (e : D ≃ₐ[ℂ] DirectMatrixSum d) :
    Nonempty (D ≃⋆ₐ[ℂ] DirectMatrixSum d) := by
  choose c hc using fun i ↦ exists_blockIntertwiningAlgEquiv d e i
  let cProd : DirectMatrixSum d ≃ₐ[ℂ] DirectMatrixSum d :=
    AlgEquiv.piCongrRight c
  let correctedAlg : D ≃ₐ[ℂ] DirectMatrixSum d := e.trans cProd
  refine ⟨StarAlgEquiv.ofAlgEquiv correctedAlg ?_⟩
  intro x
  funext i
  change c i (e (star x) i) = star (c i (e x i))
  have heStar : e (star x) = transportedInvolution e (e x) := by
    simp [transportedInvolution]
  rw [congrFun heStar i, transportedInvolution_apply]
  exact hc i (e x i)

/-- Every finite-dimensional complex C-star algebra is star-isomorphic to a
finite product of nonzero full matrix algebras. -/
theorem exists_starAlgEquiv_directMatrixSum_of_finiteDimensionalCStar
    (D : Type*) [CStarAlgebra D] [FiniteDimensional ℂ D] :
    ∃ (r : ℕ) (d : Fin r → ℕ) (hne : ∀ i, Nonempty (Fin (d i))),
      letI : ∀ i, Nonempty (Fin (d i)) := hne
      Nonempty (D ≃⋆ₐ[ℂ] DirectMatrixSum d) := by
  obtain ⟨r, d, hd, ⟨e⟩⟩ :=
    exists_algEquiv_directMatrixSum_of_finiteDimensionalCStar D
  have hne : ∀ i, Nonempty (Fin (d i)) := fun i ↦
    Fin.pos_iff_nonempty.mp (NeZero.pos (d i))
  letI : ∀ i, Nonempty (Fin (d i)) := hne
  exact ⟨r, d, hne, exists_correctedStarAlgEquiv_to_directMatrixSum d e⟩

/-- Every completely positive contraction from an arbitrary
finite-dimensional complex C-star algebra to the concrete matrix corona has
an exact completely positive contractive lift. -/
theorem exists_completelyPositiveContractive_lift_of_finiteDimensionalCStar
    {D : Type*} [CStarAlgebra D] [FiniteDimensional ℂ D]
    {X : ℕ → Type*} [∀ n, Fintype (X n)] [∀ n, DecidableEq (X n)]
    [∀ n, Nonempty (X n)]
    (f : D →ₗ[ℂ] NormMatrixCStarCorona X)
    (hf : CStarExactness.IsCompletelyPositive f)
    (hcontract : ∀ x, ‖f x‖ ≤ ‖x‖) :
    ∃ lift : D →ₗ[ℂ] BoundedMatrixSequence X,
      CStarExactness.IsCompletelyPositive lift ∧
      (∀ x, ‖lift x‖ ≤ ‖x‖) ∧
      ∀ x, normMatrixCStarCoronaQuotient X (lift x) = f x := by
  obtain ⟨r, d, hne, ⟨e⟩⟩ :=
    exists_starAlgEquiv_directMatrixSum_of_finiteDimensionalCStar D
  letI : ∀ i, Nonempty (Fin (d i)) := hne
  exact exists_completelyPositiveContractive_lift_of_starAlgEquiv_directMatrixSum
    d X e f hf hcontract

end
end BlackadarKirchberg
end GroupApproximation

open GroupApproximation.BlackadarKirchberg

#audit_axioms transportedInvolution_single
#audit_axioms blockTransportedInvolution_gram_eq_zero_iff
#audit_axioms blockFullMatrixInvolutionData
#audit_axioms exists_blockIntertwiningAlgEquiv
#audit_axioms exists_correctedStarAlgEquiv_to_directMatrixSum
#audit_axioms exists_starAlgEquiv_directMatrixSum_of_finiteDimensionalCStar
#audit_axioms exists_completelyPositiveContractive_lift_of_finiteDimensionalCStar
