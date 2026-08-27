import GroupApproximation.Sofic.FiniteGroupUlamIteration
import GroupApproximation.Sofic.OperatorMF

/-!
# Exactifying a finite subgroup in a norm-matrix corona

An arbitrary coordinate unitary lift of a homomorphism from a finite group has
total multiplication defect tending to zero.  The constructive Ulam theorem
then replaces every sufficiently late coordinate table by an exact
same-dimension representation.  The replacement is norm-null, so it represents
the original corona homomorphism.
-/

namespace GroupApproximation
namespace FiniteGroupCoronaExactification

open Filter Matrix FiniteGroupUlamStep FiniteGroupUlamIteration
open scoped Topology Matrix.Norms.L2Operator

noncomputable section

universe u

variable {F : Type u} [Group F] [Fintype F]
variable {X : ℕ → FiniteModel}

noncomputable local instance matrixBlockCStarAlgebra
    (Y : Type) [Fintype Y] [DecidableEq Y] [Nonempty Y] :
    CStarAlgebra (Matrix Y Y ℂ) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

omit [Group F] in
/-- A single nonnegative entry is bounded by the sum of a finite square. -/
theorem le_double_sum (d : F → F → ℝ) (hd : ∀ g h, 0 ≤ d g h) (g h : F) :
    d g h ≤ ∑ g' : F, ∑ h' : F, d g' h' := by
  calc
    d g h ≤ ∑ h' : F, d g h' :=
      Finset.single_le_sum (s := Finset.univ) (f := fun h' ↦ d g h')
        (fun _ _ ↦ hd _ _) (Finset.mem_univ h)
    _ ≤ ∑ g' : F, ∑ h' : F, d g' h' :=
      Finset.single_le_sum (s := Finset.univ) (f := fun g' ↦ ∑ h' : F, d g' h')
        (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ hd _ _) (Finset.mem_univ g)

/-- Reinterpret a matrix-unitary-group element using the C-star matrix star
instance.  The underlying matrix is unchanged. -/
def matrixUnitaryToCStar {Y : FiniteModel}
    [Nonempty Y] (u : Matrix.unitaryGroup Y ℂ) : unitary (Matrix Y Y ℂ) := by
  refine ⟨u, ?_⟩
  change (u : Matrix Y Y ℂ) ∈ Matrix.unitaryGroup Y ℂ
  exact u.prop

/-- Reinterpret a C-star unitary as a matrix-unitary-group element. -/
def cstarUnitaryToMatrix {Y : FiniteModel}
    [Nonempty Y] (u : unitary (Matrix Y Y ℂ)) : Matrix.unitaryGroup Y ℂ := by
  refine ⟨u, ?_⟩
  change ((u : unitary (Matrix Y Y ℂ)) : Matrix Y Y ℂ) ∈
    unitary (Matrix Y Y ℂ)
  exact u.prop

/-- The reinterpretation is multiplicative. -/
def cstarUnitaryToMatrixHom {Y : FiniteModel} [Nonempty Y] :
    unitary (Matrix Y Y ℂ) →* Matrix.unitaryGroup Y ℂ where
  toFun := cstarUnitaryToMatrix
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Sum of all coordinate multiplication defects of a finite packet. -/
def totalDefect
    (lift : F → ∀ n, Matrix.unitaryGroup (X n) ℂ) (n : ℕ) : ℝ :=
  ∑ g : F, ∑ h : F,
    ‖(lift (g * h) n : Matrix (X n) (X n) ℂ) -
      (lift g n : Matrix (X n) (X n) ℂ) * lift h n‖

theorem totalDefect_nonneg
    (lift : F → ∀ n, Matrix.unitaryGroup (X n) ℂ) (n : ℕ) :
    0 ≤ totalDefect lift n := by
  unfold totalDefect
  positivity

theorem coordinateDefect_le_totalDefect
    (lift : F → ∀ n, Matrix.unitaryGroup (X n) ℂ) (n : ℕ) (g h : F) :
    ‖(lift (g * h) n : Matrix (X n) (X n) ℂ) -
      (lift g n : Matrix (X n) (X n) ℂ) * lift h n‖ ≤ totalDefect lift n := by
  unfold totalDefect
  let d : F → F → ℝ := fun g' h' ↦
    ‖(lift (g' * h') n : Matrix (X n) (X n) ℂ) -
      (lift g' n : Matrix (X n) (X n) ℂ) * lift h' n‖
  change d g h ≤ ∑ g' : F, ∑ h' : F, d g' h'
  exact le_double_sum d (fun _ _ ↦ norm_nonneg _) g h

omit [Fintype F] in
/-- Every fixed coordinate multiplication defect tends to zero. -/
theorem coordinateDefect_tendsto_zero
    (rho : F →* NormMatrixCoronaUnitary X)
    (lift : F → ∀ n, Matrix.unitaryGroup (X n) ℂ)
    (hlift : ∀ g, QuotientGroup.mk (lift g) = rho g) (g h : F) :
    Tendsto (fun n ↦
      ‖(lift (g * h) n : Matrix (X n) (X n) ℂ) -
        (lift g n : Matrix (X n) (X n) ℂ) * lift h n‖) cofinite (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [normMatrixCorona_lift_eventually_multiplicative X rho lift hlift
      g h (ε / 2) (by positivity)] with n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  linarith

/-- The total finite-packet defect tends to zero. -/
theorem totalDefect_tendsto_zero
    (rho : F →* NormMatrixCoronaUnitary X)
    (lift : F → ∀ n, Matrix.unitaryGroup (X n) ℂ)
    (hlift : ∀ g, QuotientGroup.mk (lift g) = rho g) :
    Tendsto (totalDefect lift) cofinite (𝓝 0) := by
  unfold totalDefect
  simpa using tendsto_finsetSum Finset.univ fun g _ ↦
    tendsto_finsetSum Finset.univ fun h _ ↦
      coordinateDefect_tendsto_zero rho lift hlift g h

/-- Exact same-dimension representation at coordinate `n`; before the defect
is small enough, use the trivial representation. -/
def exactCoordinate (hX : ∀ n, Nonempty (X n))
    (lift : F → ∀ n, Matrix.unitaryGroup (X n) ℂ) (n : ℕ) :
    F →* Matrix.unitaryGroup (X n) ℂ := by
  classical
  letI : Nonempty (X n) := hX n
  let table : F → unitary (Matrix (X n) (X n) ℂ) :=
    fun g ↦ matrixUnitaryToCStar (lift g n)
  have htable : MultiplicativeDefectAtMost (F := F)
      (A := Matrix (X n) (X n) ℂ) table (totalDefect lift n) := by
    intro g h
    simpa [table, matrixUnitaryToCStar] using
      coordinateDefect_le_totalDefect lift n g h
  by_cases hsmall : totalDefect lift n ≤ 1 / 52
  · exact cstarUnitaryToMatrixHom.comp
      (exactifiedRepresentation table (totalDefect_nonneg lift n) hsmall htable)
  · exact 1

theorem exactCoordinate_sub_lift_le
    (hX : ∀ n, Nonempty (X n))
    (lift : F → ∀ n, Matrix.unitaryGroup (X n) ℂ)
    (n : ℕ) (hsmall : totalDefect lift n ≤ 1 / 52) (g : F) :
    ‖((exactCoordinate hX lift n g : Matrix.unitaryGroup (X n) ℂ) :
          Matrix (X n) (X n) ℂ) - lift g n‖ ≤ 12 * totalDefect lift n := by
  classical
  letI : Nonempty (X n) := hX n
  let table : F → unitary (Matrix (X n) (X n) ℂ) :=
    fun x ↦ matrixUnitaryToCStar (lift x n)
  have htable : MultiplicativeDefectAtMost (F := F)
      (A := Matrix (X n) (X n) ℂ) table (totalDefect lift n) := by
    intro g h
    simpa [table, matrixUnitaryToCStar] using
      coordinateDefect_le_totalDefect lift n g h
  rw [exactCoordinate]
  simp only [dif_pos hsmall]
  exact norm_exactifiedRepresentation_sub_le table
    (totalDefect_nonneg lift n) hsmall
    htable g

/-- The exact coordinate representations give the original corona
homomorphism. -/
theorem quotient_mk_exactCoordinate
    (hX : ∀ n, Nonempty (X n))
    (rho : F →* NormMatrixCoronaUnitary X)
    (lift : F → ∀ n, Matrix.unitaryGroup (X n) ℂ)
    (hlift : ∀ g, QuotientGroup.mk (lift g) = rho g) (g : F) :
    QuotientGroup.mk (fun n ↦ exactCoordinate hX lift n g) = rho g := by
  rw [← hlift g]
  apply QuotientGroup.eq.mpr
  intro ε hε
  have htotal := totalDefect_tendsto_zero rho lift hlift
  have heventSmall : ∀ᶠ n in cofinite, totalDefect lift n ≤ 1 / 52 := by
    have := (Metric.tendsto_nhds.1 htotal) (1 / 52) (by norm_num)
    filter_upwards [this] with n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (totalDefect_nonneg lift n)] at hn
    exact hn.le
  have heventEps : ∀ᶠ n in cofinite, 12 * totalDefect lift n < ε := by
    have := (Metric.tendsto_nhds.1 htotal) (ε / 12) (by positivity)
    filter_upwards [this] with n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (totalDefect_nonneg lift n)] at hn
    nlinarith
  filter_upwards [heventSmall, heventEps] with n hnsmall hnε
  change opLength (X n) ((exactCoordinate hX lift n g)⁻¹ * lift g n) < ε
  rw [opLength_inv_mul]
  exact (by
    rw [norm_sub_rev]
    exact (exactCoordinate_sub_lift_le hX lift n hnsmall g).trans_lt hnε)

/-- Every finite-group corona representation has exact coordinate lifts in
the original matrix dimensions. -/
theorem exists_exact_coordinate_lift
    (hX : ∀ n, Nonempty (X n))
    (rho : F →* NormMatrixCoronaUnitary X) :
    ∃ lift : ∀ n, F →* Matrix.unitaryGroup (X n) ℂ,
      ∀ g, QuotientGroup.mk (fun n ↦ lift n g) = rho g := by
  classical
  choose rawLift hrawLift using fun g : F ↦ QuotientGroup.mk_surjective (rho g)
  exact ⟨fun n ↦ exactCoordinate hX rawLift n,
    quotient_mk_exactCoordinate hX rho rawLift hrawLift⟩

end

end FiniteGroupCoronaExactification
end GroupApproximation
