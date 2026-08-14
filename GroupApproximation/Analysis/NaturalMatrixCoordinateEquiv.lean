import GroupApproximation.Analysis.NormMatrixCoronaUnitary
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Reindexing norm-matrix coronas by natural dimensions

Every finite matrix coordinate is reindexed along its canonical equivalence
with `Fin` of the same cardinality.  The resulting equivalences preserve the
operator norm, the null-sequence subgroup, and hence both the unitary-sequence
corona and the genuine C-star-corona unitary group.
-/

namespace GroupApproximation

noncomputable section

open scoped CStarAlgebra Matrix.Norms.L2Operator

noncomputable local instance matrixCStarAlgebra
    (n : Type) [Fintype n] [DecidableEq n] :
    CStarAlgebra (Matrix n n ℂ) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

/-- The canonical finite model underlying the literal matrix algebra
`M_d(ℂ)`. -/
abbrev naturalFiniteModel (d : ℕ) : FiniteModel where
  carrier := Fin d
  fintype := inferInstance
  decidableEq := inferInstance

@[simp] theorem card_naturalFiniteModel (d : ℕ) :
    Fintype.card (naturalFiniteModel d) = d := by
  simp [naturalFiniteModel]

/-- Reindexing rows and columns by the same finite-set equivalence is a
star-algebra equivalence for complex matrices. -/
def matrixReindexStarAlgEquiv
    {m n : Type} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (e : m ≃ n) :
    Matrix m m ℂ ≃⋆ₐ[ℂ] Matrix n n ℂ :=
  StarAlgEquiv.ofAlgEquiv (Matrix.reindexAlgEquiv ℂ ℂ e) (by
    intro A
    ext i j
    rfl)

/-- Reindexing a finite complex matrix along a basis bijection preserves its
operator norm. -/
theorem norm_matrixReindexStarAlgEquiv
    {m n : Type} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (e : m ≃ n) (A : Matrix m m ℂ) :
    ‖matrixReindexStarAlgEquiv e A‖ = ‖A‖ :=
  StarAlgEquiv.norm_map (matrixReindexStarAlgEquiv e) A

/-- Reindexing a finite matrix basis induces a multiplicative equivalence of
unitary groups. -/
noncomputable def unitaryReindexEquiv
    {m n : Type} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (e : m ≃ n) :
    Matrix.unitaryGroup m ℂ ≃* Matrix.unitaryGroup n ℂ :=
  (Unitary.mapEquiv
    (StarMulEquiv.ofClass (matrixReindexStarAlgEquiv e))).toMulEquiv

/-- Reindexing preserves operator-norm displacement from the identity. -/
theorem opLength_unitaryReindexEquiv
    {m n : Type} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (e : m ≃ n)
    (u : Matrix.unitaryGroup m ℂ) :
    opLength (⟨n, inferInstance, inferInstance⟩ : FiniteModel)
        (unitaryReindexEquiv e u) =
      opLength (⟨m, inferInstance, inferInstance⟩ : FiniteModel) u := by
  change ‖(matrixReindexStarAlgEquiv e) (u : Matrix m m ℂ) - 1‖ =
    ‖(u : Matrix m m ℂ) - 1‖
  rw [← map_one (matrixReindexStarAlgEquiv e), ← map_sub,
    norm_matrixReindexStarAlgEquiv]

/-- Replace every finite coordinate set by the literal natural basis of the
same cardinality. -/
abbrev naturalizedModel (X : ℕ → FiniteModel) (n : ℕ) : FiniteModel :=
  naturalFiniteModel (Fintype.card (X n))

noncomputable instance naturalizedModelNonempty
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)] (n : ℕ) :
    Nonempty (naturalizedModel X n) :=
  ⟨⟨0, Fintype.card_pos⟩⟩

/-- Coordinatewise basis reindexing of unitary matrix sequences. -/
noncomputable def unitarySequenceNaturalizeEquiv (X : ℕ → FiniteModel) :
    (∀ n, Matrix.unitaryGroup (X n) ℂ) ≃*
      (∀ n, Matrix.unitaryGroup (naturalizedModel X n) ℂ) :=
  MulEquiv.piCongrRight fun n ↦ unitaryReindexEquiv (Fintype.equivFin (X n))

@[simp] theorem opLength_unitarySequenceNaturalizeEquiv_apply
    (X : ℕ → FiniteModel)
    (u : ∀ n, Matrix.unitaryGroup (X n) ℂ) (n : ℕ) :
    opLength (naturalizedModel X n)
        (unitarySequenceNaturalizeEquiv X u n) =
      opLength (X n) (u n) := by
  exact opLength_unitaryReindexEquiv (Fintype.equivFin (X n)) (u n)

@[simp] theorem opLength_unitarySequenceNaturalizeEquiv_symm_apply
    (X : ℕ → FiniteModel)
    (v : ∀ n, Matrix.unitaryGroup (naturalizedModel X n) ℂ) (n : ℕ) :
    opLength (X n) ((unitarySequenceNaturalizeEquiv X).symm v n) =
      opLength (naturalizedModel X n) (v n) := by
  have h := opLength_unitarySequenceNaturalizeEquiv_apply X
    ((unitarySequenceNaturalizeEquiv X).symm v) n
  simpa using h.symm

/-- Coordinatewise basis reindexing carries the null-sequence subgroup
exactly onto the null-sequence subgroup. -/
theorem map_nullCofiniteOpSubgroup_unitarySequenceNaturalizeEquiv
    (X : ℕ → FiniteModel) :
    (nullCofiniteOpSubgroup X).map (unitarySequenceNaturalizeEquiv X) =
      nullCofiniteOpSubgroup (naturalizedModel X) := by
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    intro ε hε
    filter_upwards [hu ε hε] with n hn
    exact (opLength_unitarySequenceNaturalizeEquiv_apply X u n).symm ▸ hn
  · intro hv
    refine ⟨(unitarySequenceNaturalizeEquiv X).symm v, ?_, by simp⟩
    intro ε hε
    filter_upwards [hv ε hε] with n hn
    exact (opLength_unitarySequenceNaturalizeEquiv_symm_apply X v n).symm ▸ hn

/-- Every basis-free unitary-sequence corona is canonically equivalent to a
corona whose coordinates are literally `Fin (card X_n)`. -/
noncomputable def normMatrixCoronaNaturalizeEquiv (X : ℕ → FiniteModel) :
    NormMatrixCoronaUnitary X ≃*
      NormMatrixCoronaUnitary (naturalizedModel X) :=
  QuotientGroup.congr (nullCofiniteOpSubgroup X)
    (nullCofiniteOpSubgroup (naturalizedModel X))
    (unitarySequenceNaturalizeEquiv X)
    (map_nullCofiniteOpSubgroup_unitarySequenceNaturalizeEquiv X)

/-- Combining sequence reindexing with polar correction gives a canonical
equivalence between the genuine C-star-corona unitary groups before and
after replacement by literal natural matrix dimensions. -/
noncomputable def actualCoronaNaturalizeEquiv
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)] :
    unitary (NormMatrixCStarCorona (fun n ↦ X n)) ≃*
      unitary (NormMatrixCStarCorona
        (fun n ↦ naturalizedModel X n)) := by
  exact (normMatrixCoronaUnitaryEquiv X).symm.trans
    ((normMatrixCoronaNaturalizeEquiv X).trans
      (normMatrixCoronaUnitaryEquiv (naturalizedModel X)))

end

end GroupApproximation
