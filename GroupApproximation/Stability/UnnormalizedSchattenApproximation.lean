import GroupApproximation.Meta.AxiomGuard
import GroupApproximation.Stability.LinearMetricApproximation
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.Matrix.Normed

/-!
# Unnormalized Schatten approximation and stability

This file states the finite-Schatten approximation and stability predicates
literally.  The approximation predicate uses one sequence of maps and positive
`limsup` displacement for every nonidentity element.  All matrix dimensions
are positive.

For arbitrary real `p`, the unnormalized Schatten `p`-distance is defined from
the singular values.  The residual-finiteness implication does not require the
Schatten triangle inequality.  Indeed, the approximation maps are normalized
at the identity.  If the nearby homomorphism killed a separated element, its
distance from the approximation map at that element would therefore be exactly
the element's displacement from the identity.

At `p = 2`, the Schatten norm is the Frobenius norm.  Mathlib supplies the
Frobenius normed-group structure, so the stability-plus-approximation argument
is proved unconditionally in that case by the generic linear-metric theorem.
-/

namespace GroupApproximation
namespace UnnormalizedSchattenApproximation

open Filter

universe u

/-- A positive finite matrix dimension. -/
abbrev PositiveDimension := {d : ℕ // 0 < d}

/-- The unitary group in a specified positive dimension. -/
abbrev UnitaryTarget (d : PositiveDimension) :=
  Matrix.unitaryGroup (Fin d.1) ℂ

/-- The unnormalized Schatten `p`-norm, defined as the `ℓᵖ`-norm of the
singular-value list.  No normalization by the matrix dimension occurs. -/
noncomputable def schattenPNorm (p : ℝ) {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  Real.rpow
    (∑ k ∈ Finset.range d,
      Real.rpow ((Matrix.toEuclideanLin A).singularValues k) p)
    (1 / p)

/-- The unnormalized Schatten `p`-distance between two unitary matrices. -/
noncomputable def schattenPDist (p : ℝ) {d : PositiveDimension}
    (U V : UnitaryTarget d) : ℝ :=
  schattenPNorm p
    ((U : Matrix (Fin d.1) (Fin d.1) ℂ) -
      (V : Matrix (Fin d.1) (Fin d.1) ℂ))

/-- The singular-value formula for the unnormalized Schatten quantity is
nonnegative for every real exponent. -/
theorem schattenPNorm_nonneg (p : ℝ) {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℂ) : 0 ≤ schattenPNorm p A := by
  exact Real.rpow_nonneg
    (Finset.sum_nonneg fun k _ ↦
      Real.rpow_nonneg
        ((Matrix.toEuclideanLin A).singularValues_nonneg k) p)
    (1 / p)

/-- Unnormalized Schatten displacement is nonnegative. -/
theorem schattenPDist_nonneg (p : ℝ) {d : PositiveDimension}
    (U V : UnitaryTarget d) : 0 ≤ schattenPDist p U V :=
  schattenPNorm_nonneg p _

/-- A single sequence of maps into positive-dimensional unitary groups whose
multiplicative defects vanish in unnormalized Schatten `p`-distance. -/
structure AlmostRepresentation (p : ℝ) (G : Type u) [Group G] where
  dimension : ℕ → PositiveDimension
  map : ∀ n, G → UnitaryTarget (dimension n)
  asymptoticallyMultiplicative :
    ∀ g h : G, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
      schattenPDist p (map n (g * h)) (map n g * map n h) < ε

/-- Literal one-sequence approximation in unnormalized Schatten `p`-distance.
Every map sends the identity to the identity, and every nonidentity element
has positive `limsup` displacement from the target identity. -/
def IsApproximated (p : ℝ) (G : Type u) [Group G] : Prop :=
  ∃ A : AlmostRepresentation p G,
    (∀ n, A.map n 1 = 1) ∧
      ∀ g : G, g ≠ 1 →
        0 < Filter.limsup
          (fun n ↦ schattenPDist p (A.map n g) 1) Filter.atTop

/-- Literal pointwise stability in unnormalized Schatten `p`-distance. -/
def IsStable (p : ℝ) (G : Type u) [Group G] : Prop :=
  ∀ A : AlmostRepresentation p G,
    ∃ π : ∀ n, G →* UnitaryTarget (A.dimension n),
      ∀ g : G, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
        schattenPDist p (A.map n g) (π n g) < ε

/-- The precise general finite-Schatten residual-finiteness implication. -/
def StabilityForcesResidualFiniteness (p : ℝ) : Prop :=
  1 ≤ p → ∀ (G : Type u) [Group G] [Group.FG G],
    IsApproximated p G → IsStable p G → Group.ResiduallyFinite G

/-- Approximation and stability in the literal unnormalized Schatten
`p`-quantity force residual finiteness.  The proof is valid for every real
`p`; the hypothesis `1 ≤ p` in `StabilityForcesResidualFiniteness` only records
the finite-Schatten range of the printed statement.

No triangle inequality is used.  Positive `limsup` separation supplies a
subsequence on which a fixed nonidentity element stays away from the identity.
Stability supplies nearby homomorphisms.  Since a homomorphism sends the
identity to the identity, any one of those homomorphisms which killed the
element would make its approximation error equal to the separated
displacement.  The resulting detecting linear representation is converted to
a finite quotient by the formalized Mal'cev theorem. -/
theorem residuallyFinite_of_approximated_of_stable
    {p : ℝ} {G : Type u} [Group G] [Group.FG G]
    (happrox : IsApproximated p G) (hstable : IsStable p G) :
    Group.ResiduallyFinite G := by
  classical
  obtain ⟨A, _hone, hseparate⟩ := happrox
  obtain ⟨π, hπ⟩ := hstable A
  apply Group.residuallyFinite_of_forall_exists_finite_monoidHom
  intro x hx
  let L := Filter.limsup
    (fun n ↦ schattenPDist p (A.map n x) 1) Filter.atTop
  have hL : 0 < L := hseparate x hx
  have hcob : Filter.IsCoboundedUnder (· ≤ ·) Filter.atTop
      (fun n ↦ schattenPDist p (A.map n x) 1) :=
    Filter.isCoboundedUnder_le_of_le Filter.atTop fun n ↦
      schattenPDist_nonneg p (A.map n x) 1
  have hfrequent : ∃ᶠ n in Filter.atTop,
      L / 2 < schattenPDist p (A.map n x) 1 :=
    Filter.frequently_lt_of_lt_limsup hcob (by linarith)
  obtain ⟨r, hr, hgap⟩ := Filter.extraction_of_frequently_atTop hfrequent
  obtain ⟨N, hN⟩ := hπ x (L / 2) (by linarith)
  have hclose :
      schattenPDist p (A.map (r N) x) (π (r N) x) < L / 2 :=
    hN (r N) (hr.id_le N)
  have hπx : π (r N) x ≠ 1 := by
    intro heq
    have hsmall : schattenPDist p (A.map (r N) x) 1 < L / 2 := by
      simpa [heq] using hclose
    exact (not_lt_of_ge (hgap N).le) hsmall
  let ρ : G →* Matrix.GeneralLinearGroup (Fin (A.dimension (r N)).1) ℂ :=
    Unitary.toUnits.comp (π (r N))
  have hρx : ρ x ≠ 1 := by
    intro h
    apply hπx
    apply Unitary.toUnits_injective
    simpa [ρ] using h
  haveI : Group.ResiduallyFinite ρ.range :=
    MalcevLinear.residuallyFinite_of_fg ρ.range
      (LinearMetricApproximation.range_fg ρ)
  let y : ρ.range := ρ.rangeRestrict x
  have hy : y ≠ 1 := by
    intro h
    apply hρx
    exact Subtype.ext_iff.mp h
  obtain ⟨N', hN'⟩ := Group.exists_finiteIndexNormalSubgroup_notMem y hy
  letI := N'.isNormal'
  letI := N'.isFiniteIndex'
  refine ⟨ρ.range ⧸ N'.toSubgroup, inferInstance, inferInstance,
    (QuotientGroup.mk' N'.toSubgroup).comp ρ.rangeRestrict, ?_⟩
  intro h
  apply hN'
  exact (QuotientGroup.eq_one_iff y).mp (by simpa [y] using h)

/-- The unconditional all-finite-`p` stability principle. -/
theorem stabilityForcesResidualFiniteness (p : ℝ) :
    StabilityForcesResidualFiniteness.{u} p := by
  intro _hp G _ _ happrox hstable
  exact residuallyFinite_of_approximated_of_stable happrox hstable

/-- Closed proposition expressing the stability implication simultaneously
for every finite Schatten parameter. -/
def AllFinitePStabilityForcesResidualFiniteness : Prop :=
  ∀ p : ℝ, StabilityForcesResidualFiniteness.{u} p

theorem allFinitePStabilityForcesResidualFiniteness :
    AllFinitePStabilityForcesResidualFiniteness.{u} := by
  exact stabilityForcesResidualFiniteness

/-! ## The unconditional `p = 2` specialization -/

/-- The unnormalized Schatten `2`-distance, written in its Frobenius
coordinate formula. -/
noncomputable def schattenTwoDist {d : PositiveDimension}
    (U V : UnitaryTarget d) : ℝ :=
  Real.rpow
    (∑ i : Fin d.1, ∑ j : Fin d.1,
      ‖(U : Matrix (Fin d.1) (Fin d.1) ℂ) i j - V i j‖ ^ (2 : ℝ))
    (1 / 2 : ℝ)

/-- The metric on a finite unitary group induced by the unnormalized
Frobenius norm on matrices. -/
@[reducible] noncomputable def schattenTwoMetricSpace (d : PositiveDimension) :
    MetricSpace (UnitaryTarget d) := by
  letI : NormedAddCommGroup (Matrix (Fin d.1) (Fin d.1) ℂ) :=
    Matrix.frobeniusNormedAddCommGroup
  exact MetricSpace.induced
    (fun U : UnitaryTarget d ↦ (U : Matrix (Fin d.1) (Fin d.1) ℂ))
    Subtype.coe_injective inferInstance

/-- The induced metric is exactly the displayed unnormalized Schatten
`2`-distance. -/
theorem dist_eq_schattenTwoDist (d : PositiveDimension) (U V : UnitaryTarget d) :
    @dist (UnitaryTarget d) (schattenTwoMetricSpace d).toDist U V =
      schattenTwoDist U V := by
  letI : NormedAddCommGroup (Matrix (Fin d.1) (Fin d.1) ℂ) :=
    Matrix.frobeniusNormedAddCommGroup
  change dist
    (U : Matrix (Fin d.1) (Fin d.1) ℂ)
    (V : Matrix (Fin d.1) (Fin d.1) ℂ) = _
  rw [dist_eq_norm, Matrix.frobenius_norm_def]
  rfl

/-- One-sequence approximation by positive-dimensional unitary groups in the
unnormalized Schatten `2` metric. -/
noncomputable def IsSchattenTwoApproximated (G : Type u) [Group G] : Prop := by
  letI : ∀ d : PositiveDimension, PseudoMetricSpace ↑(UnitaryTarget d) :=
    fun d ↦ (schattenTwoMetricSpace d).toPseudoMetricSpace
  exact LinearMetricApproximation.IsLimsupApproximatedBy
    (I := PositiveDimension) (M := fun d ↦ ↑(UnitaryTarget d)) G

/-- Pointwise stability for the same unnormalized Schatten `2` models. -/
noncomputable def IsSchattenTwoStable (G : Type u) [Group G] : Prop := by
  letI : ∀ d : PositiveDimension, PseudoMetricSpace ↑(UnitaryTarget d) :=
    fun d ↦ (schattenTwoMetricSpace d).toPseudoMetricSpace
  exact LinearMetricApproximation.IsStableWithRespectTo
    (I := PositiveDimension) (M := fun d ↦ ↑(UnitaryTarget d)) G

/-- The closed, unconditional Schatten-`2` stability principle.  The
approximation and stability clauses occur inside the proposition; no group or
literature theorem is supplied as construction data to its proof. -/
def SchattenTwoStabilityPrinciple : Prop :=
  ∀ (G : Type u) [Group G] [Group.FG G],
    IsSchattenTwoApproximated G → IsSchattenTwoStable G →
      Group.ResiduallyFinite G

theorem schattenTwoStabilityPrinciple : SchattenTwoStabilityPrinciple := by
  intro G _ _ happrox hstable
  letI : ∀ d : PositiveDimension, PseudoMetricSpace ↑(UnitaryTarget d) :=
    fun d ↦ (schattenTwoMetricSpace d).toPseudoMetricSpace
  apply LinearMetricApproximation.residuallyFinite_of_limsupApproximated_of_stable
    (I := PositiveDimension) (M := fun d ↦ ↑(UnitaryTarget d))
    (F := fun _ ↦ ℂ) (d := fun d ↦ d.1)
    (linear := fun _ ↦ Unitary.toUnits)
    (linear_injective := fun _ ↦ Unitary.toUnits_injective)
  · simpa [IsSchattenTwoApproximated] using happrox
  · simpa [IsSchattenTwoStable] using hstable

#audit_axioms dist_eq_schattenTwoDist
#audit_closed_axioms allFinitePStabilityForcesResidualFiniteness
#audit_closed_axioms schattenTwoStabilityPrinciple

end UnnormalizedSchattenApproximation
end GroupApproximation
