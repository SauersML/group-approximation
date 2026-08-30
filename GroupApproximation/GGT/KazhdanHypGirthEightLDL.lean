import GroupApproximation.GGT.KazhdanHypGirthEight

/-!
# Exact LDL certificates for the girth-eight spectral probe

`GGT/KazhdanHypGirthEight.lean` deliberately asks a successful spectral probe
for rational Gram rows.  Numerical SDP packages more naturally return a
rationalized `L D Lᵀ` factorization: the columns of `L` are rational, while
the diagonal entries of `D` are nonnegative rationals which need not themselves
be rational squares.

This file is the exact adapter between those two output formats.  A
`RationalLDLFactor M Pivot` certifies

```
  M u v = ∑ p, diagonal p * lower p u * lower p v
```

pointwise over `ℚ`.  Lagrange's four-square theorem, already formalized as
`TriangularHodgeLayer.exists_four_square_factor`, replaces every nonnegative
diagonal weight by four rational Gram rows.  Thus the finite probe never has to
guess square roots and the trusted boundary remains the exact rational
factorization identity.

No witness existence is asserted here.  For a proposed positive triangle
table, a probe must still supply the finite `GirthEightChecks` and an actual
LDL certificate for the normalized-link residual.
-/

set_option linter.unusedSectionVars false

namespace GroupApproximation
namespace KazhdanHyp

/-! ## A rational LDL factor and its rational Gram rows -/

/-- An exact rational `L D Lᵀ` factorization of a finite matrix, with every
diagonal weight certified nonnegative.  `Pivot` may contain redundant or
zero-weight columns; no rank or triangularity condition is needed by the Gram
identity consumed downstream. -/
structure RationalLDLFactor {V : Type} [Fintype V]
    (M : V → V → ℚ) (Pivot : Type) [Fintype Pivot] where
  /-- The rational columns of `L`. -/
  lower : Pivot → V → ℚ
  /-- The rational diagonal of `D`. -/
  diagonal : Pivot → ℚ
  /-- Positive semidefiniteness, reduced to scalar rational inequalities. -/
  diagonal_nonneg : ∀ p, 0 ≤ diagonal p
  /-- The exact pointwise residual identity. -/
  factorization : ∀ u v,
    M u v = ∑ p, diagonal p * lower p u * lower p v

namespace RationalLDLFactor

variable {V Pivot : Type} [Fintype V] [Fintype Pivot]
  {M : V → V → ℚ} (C : RationalLDLFactor M Pivot)

/-- Four rational square roots of one diagonal weight. -/
noncomputable def fourSquare (p : Pivot) : Fin 4 → ℚ :=
  Classical.choose
    (TriangularHodgeLayer.exists_four_square_factor
      (C.diagonal p) (C.diagonal_nonneg p))

/-- The chosen four squares add back to the diagonal weight. -/
theorem sum_sq_fourSquare (p : Pivot) :
    ∑ k, C.fourSquare p k ^ 2 = C.diagonal p :=
  Classical.choose_spec
    (TriangularHodgeLayer.exists_four_square_factor
      (C.diagonal p) (C.diagonal_nonneg p))

/-- The rational Gram rows obtained from the LDL columns.  There are four rows
per pivot because a nonnegative rational need not be a rational square. -/
noncomputable def gramRows : Pivot × Fin 4 → V → ℚ :=
  fun pk v ↦ C.fourSquare pk.1 pk.2 * C.lower pk.1 v

/-- The LDL-derived rows have Gram matrix exactly `M`. -/
theorem sum_gramRows_mul (u v : V) :
    ∑ row, C.gramRows row u * C.gramRows row v = M u v := by
  classical
  rw [Fintype.sum_prod_type]
  calc
    (∑ p, ∑ k,
        C.gramRows (p, k) u * C.gramRows (p, k) v) =
        ∑ p, (∑ k, C.fourSquare p k ^ 2) *
          (C.lower p u * C.lower p v) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [gramRows]
      ring
    _ = ∑ p, C.diagonal p * (C.lower p u * C.lower p v) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [C.sum_sq_fourSquare]
    _ = M u v := by
      rw [C.factorization]
      apply Finset.sum_congr rfl
      intro p hp
      ring

end RationalLDLFactor

/-! ## The exact output contract for the finite SDP probe -/

section Probe

variable {Generator TriangleIndex Pivot : Type}
  [Fintype Generator] [DecidableEq Generator] [Nonempty Generator]
  [Fintype TriangleIndex] [DecidableEq TriangleIndex] [Fintype Pivot]

/-- The exact rationalized output expected from an LDL-based SDP probe for one
fixed table.  The factorized matrix is precisely

`L / d - gap * P₀`,

not a floating-point approximation to it. -/
structure GirthEightSDPLDLCertificate
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator)
    (d : ℕ) (gap : ℚ) (Pivot : Type) [Fintype Pivot] where
  /-- The regular degree has a valid denominator. -/
  degree_pos : 0 < d
  /-- The certified normalized gap clears Zuk's threshold. -/
  gap_gt_half : (1 : ℚ) / 2 < gap
  /-- Exact rational LDL factorization of the spectral residual. -/
  ldl : RationalLDLFactor
    (fun u v : Generator × Bool ↦
      TriangularHodgeLayer.rationalLinkLaplacian T u v / d -
        gap * TriangularHodgeLayer.meanZeroProjector u v)
    Pivot

/-- An exact LDL certificate produces the Gram-row predicate already consumed
by the Garland proof. -/
theorem girthEightSDPChecks_of_ldl
    {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator}
    {d : ℕ} {gap : ℚ}
    (C : GirthEightSDPLDLCertificate T d gap Pivot) :
    GirthEightSDPChecks T d gap C.ldl.gramRows := by
  refine ⟨C.degree_pos, C.gap_gt_half, ?_⟩
  intro u v
  unfold TriangularHodgeLayer.linkGapResidual
    TriangularHodgeLayer.gramMatrix
  rw [C.ldl.sum_gramRows_mul]
  ring

/-- Geometry and one exact rational LDL output certify property `(T)` for the
same literal triangle table. -/
theorem hasKazhdanPropertyT_of_girthEightLDL
    {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator}
    {d : ℕ} {gap : ℚ}
    (hgeom : GirthEightChecks T d)
    (C : GirthEightSDPLDLCertificate T d gap Pivot) :
    HasKazhdanPropertyT.{0, 0} (TriangularHodgeLayer.Presented T) :=
  hasKazhdanPropertyT_of_girthEightSDPChecks hgeom
    (girthEightSDPChecks_of_ldl C)

end Probe

end KazhdanHyp
end GroupApproximation
