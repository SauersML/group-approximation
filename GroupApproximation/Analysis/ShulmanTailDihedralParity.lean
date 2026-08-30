import GroupApproximation.Analysis.AbstractSpectralGap
import GroupApproximation.Analysis.NormMatrixCoronaGenericBridge
import GroupApproximation.Analysis.NormMatrixCoronaUnitary
import GroupApproximation.Analysis.ShulmanFillNormingTailAsymptoticMF
import GroupApproximation.Sofic.DihedralCoronaParity

/-!
# Odd-dimensional obstruction to a unital tail lift

The unit clause of `StarStrongTailLift` makes its selected diagonal class a
unital star homomorphism.  A finite dihedral representation in the source can
therefore be transported first to the generic reduced product, then through
the canonical matrix-corona equivalence.  If its central half-turn is `-1`,
`DihedralCoronaParity.eventually_not_odd_card` contradicts an eventually odd
sequence of selected matrix dimensions.
-/

namespace GroupApproximation
namespace ShulmanTailDihedralParity

open Filter Matrix Topology PolarLiftingGeneralCStar
open scoped Matrix.Norms.L2Operator

noncomputable section

local instance matrixBlockCStarAlgebra
    (Y : Type) [Fintype Y] [DecidableEq Y] [Nonempty Y] :
    CStarAlgebra (Matrix Y Y ℂ) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

/-- The scalar central involution in the unitary group of a C-star algebra. -/
def negOneUnitary (C : Type*) [CStarAlgebra C] : unitary C :=
  ⟨-1, by constructor <;> simp⟩

section DiagonalUnitality

universe v

variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {B : Type v} [CStarAlgebra B]
variable {iota : ∀ n, Matrix (X n) (X n) ℂ →⋆ₙₐ[ℂ] (H →L[ℂ] H)}
variable {hnorm : ∀ (n : ℕ) (x : Matrix (X n) (X n) ℂ),
  ‖iota n x‖ ≤ ‖x‖}
variable {hone : ∀ v : H,
  Tendsto (fun n ↦ iota n (1 : Matrix (X n) (X n) ℂ) v) atTop (𝓝 v)}
variable {pi : B →⋆ₐ[ℂ] (H →L[ℂ] H)}

open ShulmanFill ShulmanFill.StarStrongTailLift

variable (phi : StarStrongTailLift iota hnorm hone pi)
  (tsel nsel : ℕ → ℕ)
  (htsel : ∀ m, m ≤ tsel m)
  (hcut : ∀ m, phi.cut (tsel m) ≤ nsel m)

/-- The tail unit defect makes the selected diagonal class exactly unital. -/
theorem diagHom_one :
    diagHom phi tsel nsel htsel hcut (1 : B) = 1 := by
  have hone' :
      (1 : CStarProductCorona
        (fun m ↦ Matrix (X (nsel m)) (X (nsel m)) ℂ) cofinite) =
      cStarProductCoronaQuotient
        (fun m ↦ Matrix (X (nsel m)) (X (nsel m)) ℂ) cofinite 1 :=
    (map_one (cStarProductCoronaQuotient
      (fun m ↦ Matrix (X (nsel m)) (X (nsel m)) ℂ) cofinite)).symm
  rw [diagHom_apply, hone']
  exact quotient_diag_eq_of_tailNull phi tsel nsel htsel hcut
    (fun t ↦ phi.toFun t 1) (fun _ ↦ 1) (diagSeq phi tsel nsel 1) 1
    (fun _ ↦ rfl) (fun _ ↦ rfl) phi.tail_one

/-- The selected diagonal class, with the tail unit estimate installed as its
`map_one` field. -/
def diagUnitalHom :
    B →⋆ₐ[ℂ]
      CStarProductCorona
        (fun m ↦ Matrix (X (nsel m)) (X (nsel m)) ℂ) cofinite where
  toFun := diagHom phi tsel nsel htsel hcut
  map_one' := diagHom_one phi tsel nsel htsel hcut
  map_mul' := map_mul (diagHom phi tsel nsel htsel hcut)
  map_zero' := map_zero (diagHom phi tsel nsel htsel hcut)
  map_add' := map_add (diagHom phi tsel nsel htsel hcut)
  commutes' z := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      map_smul, diagHom_one]
  map_star' := map_star (diagHom phi tsel nsel htsel hcut)

end DiagonalUnitality

section CoronaTransport

variable (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]

/-- Under the canonical unitary-corona equivalence, the class of the constant
matrix sequence `-1` is the scalar unitary `-1`. -/
theorem coronaNegOne_toCStar :
    normMatrixCoronaUnitaryEquiv X
        (ExactCoronaNegativeCorner.coronaNegOne X) =
      negOneUnitary (NormMatrixCStarCorona (fun n ↦ X n)) := by
  change unitarySequenceToCorona X
      (ExactCoronaNegativeCorner.negOneSeq X) = _
  apply Subtype.ext
  change normMatrixCStarCoronaMk (fun n ↦ X n)
      (unitarySequenceBounded X (ExactCoronaNegativeCorner.negOneSeq X)) = -1
  have hseq :
      unitarySequenceBounded X (ExactCoronaNegativeCorner.negOneSeq X) =
        -(1 : BoundedMatrixSequence (fun n ↦ X n)) := by
    apply lp.ext
    funext n
    rfl
  rw [hseq, map_neg, map_one]

/-- The D8 parity obstruction transported across the generic/concrete corona
identification. -/
theorem eventually_not_odd_card_generic
    (rho : DihedralGroup 4 →*
      unitary (CStarProductCorona
        (fun n ↦ Matrix (X n) (X n) ℂ) cofinite))
    (hneg : rho DihedralCoronaParity.halfTurn =
      negOneUnitary (CStarProductCorona
        (fun n ↦ Matrix (X n) (X n) ℂ) cofinite)) :
    ∀ᶠ n in cofinite, ¬ Odd (Fintype.card (X n)) := by
  let rhoNorm : DihedralGroup 4 →*
      unitary (NormMatrixCStarCorona (fun n ↦ X n)) :=
    (AbstractSpectralGap.unitaryMap
      (NormMatrixCoronaGenericBridge.coronaEquiv
        (fun n ↦ (X n : Type))).toStarAlgHom).comp rho
  let rhoSequence : DihedralGroup 4 →* NormMatrixCoronaUnitary X :=
    (normMatrixCoronaUnitaryEquiv X).symm.toMonoidHom.comp rhoNorm
  apply DihedralCoronaParity.eventually_not_odd_card rhoSequence
  have hrhoNorm : rhoNorm DihedralCoronaParity.halfTurn =
      negOneUnitary (NormMatrixCStarCorona (fun n ↦ X n)) := by
    simp only [rhoNorm, MonoidHom.comp_apply, hneg]
    apply Subtype.ext
    rw [AbstractSpectralGap.unitaryMap_coe]
    change NormMatrixCoronaGenericBridge.coronaEquiv
        (fun n ↦ (X n : Type)) (-1) = -1
    simp
  change (normMatrixCoronaUnitaryEquiv X).symm
      (rhoNorm DihedralCoronaParity.halfTurn) =
    ExactCoronaNegativeCorner.coronaNegOne X
  rw [hrhoNorm, ← coronaNegOne_toCStar]
  exact (normMatrixCoronaUnitaryEquiv X).symm_apply_apply _

end CoronaTransport

section TailObstruction

universe v

variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {B : Type v} [CStarAlgebra B]
variable {iota : ∀ n, Matrix (X n) (X n) ℂ →⋆ₙₐ[ℂ] (H →L[ℂ] H)}
variable {hnorm : ∀ (n : ℕ) (x : Matrix (X n) (X n) ℂ),
  ‖iota n x‖ ≤ ‖x‖}
variable {hone : ∀ v : H,
  Tendsto (fun n ↦ iota n (1 : Matrix (X n) (X n) ℂ) v) atTop (𝓝 v)}
variable {pi : B →⋆ₐ[ℂ] (H →L[ℂ] H)}

open ShulmanFill

/-- A unital tail lift carrying a negative-half-turn D8 representation cannot
select cofinally into eventually odd matrix dimensions. -/
theorem false_of_tailLift_of_eventually_odd
    (phi : StarStrongTailLift iota hnorm hone pi)
    (tsel nsel : ℕ → ℕ)
    (htsel : ∀ m, m ≤ tsel m)
    (hcut : ∀ m, phi.cut (tsel m) ≤ nsel m)
    (hnsel : Tendsto nsel atTop atTop)
    (hodd : ∀ᶠ n in atTop, Odd (Fintype.card (X n)))
    (sigma : DihedralGroup 4 →* unitary B)
    (hsigma : sigma DihedralCoronaParity.halfTurn = negOneUnitary B) : False := by
  let rho : DihedralGroup 4 →*
      unitary (CStarProductCorona
        (fun m ↦ Matrix (X (nsel m)) (X (nsel m)) ℂ) cofinite) :=
    (AbstractSpectralGap.unitaryMap
      (diagUnitalHom phi tsel nsel htsel hcut)).comp sigma
  have hrhoNeg : rho DihedralCoronaParity.halfTurn =
      negOneUnitary (CStarProductCorona
        (fun m ↦ Matrix (X (nsel m)) (X (nsel m)) ℂ) cofinite) := by
    simp only [rho, MonoidHom.comp_apply, hsigma]
    apply Subtype.ext
    change diagUnitalHom phi tsel nsel htsel hcut (-1) = -1
    simp
  have hnot := eventually_not_odd_card_generic
    (fun m ↦ X (nsel m)) rho hrhoNeg
  rw [Nat.cofinite_eq_atTop] at hnot
  have hboth : ∀ᶠ m in atTop,
      Odd (Fintype.card (X (nsel m))) ∧
        ¬ Odd (Fintype.card (X (nsel m))) :=
    (hnsel.eventually hodd).and hnot
  obtain ⟨m, hmOdd, hmNotOdd⟩ := hboth.exists
  exact hmNotOdd hmOdd

end TailObstruction

end


end ShulmanTailDihedralParity
end GroupApproximation
