import GroupApproximation.GGT.KazhdanHypGirthEight

/-!
# A published triangle presentation with `GQ(2,2)` link

Kangaslampi--Vdovina, *Cocompact actions on hyperbolic buildings*, arXiv
`math/0506613`, lines 223--253 of the fetched source `build45.tex`, lists the
triangle presentation `T_1` on generators `x_1,...,x_15`.  This module
transcribes those fifteen ordered triples, with `x_(i+1)` represented by
`i : Fin 15`, and checks its presentation link.

The link is the incidence graph of the smallest generalized quadrangle
`GQ(2,2)`: it has thirty signed vertices, degree three, and girth eight.  The
finite proofs below are split into the regularity, simplicity, common-neighbor,
and length-three-path checks consumed by `GirthEightChecks`; no spectral
threshold is asserted.  Its normalized gap is `1/3`, below Zuk's strict
`1/2` threshold.

The proved identity `rowCommon_eq` is the point-side block of
`N N^T = 3 I + C`; `pointLineThreePathsReduced_eq_six` checks its product
with `N`.  The scratch generator independently checks both full signed
identities `A^2 = 3 I + C` and
`C^2 = 3 I - 2 C + 3 J_same`.  At `q=2` and the exact gap `1/3`, the four
square-root-free projector weights are `5/3, 2/3, 3/4, 0`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace GroupApproximation
namespace KazhdanHyp
namespace GQTwoTable

open scoped BigOperators

/-! ## The source table -/

/-- The first published `GQ(2,2)` triangle presentation, transcribed in the
order printed in Kangaslampi--Vdovina.  Every literal is positive. -/
def triangles : Fin 15 → TriangularHodgeLayer.Triangle (Fin 15) :=
  ![
    ![(0, true), (1, true), (6, true)],
    ![(0, true), (7, true), (10, true)],
    ![(0, true), (13, true), (4, true)],
    ![(1, true), (3, true), (12, true)],
    ![(11, true), (3, true), (1, true)],
    ![(3, true), (8, true), (2, true)],
    ![(5, true), (7, true), (2, true)],
    ![(13, true), (5, true), (2, true)],
    ![(11, true), (9, true), (4, true)],
    ![(12, true), (14, true), (4, true)],
    ![(11, true), (8, true), (5, true)],
    ![(10, true), (9, true), (6, true)],
    ![(13, true), (12, true), (6, true)],
    ![(8, true), (14, true), (7, true)],
    ![(10, true), (14, true), (9, true)]
  ]

/-- The table has the fifteen rows printed in the source. -/
theorem triangleCount : Fintype.card (Fin 15) = 15 := by
  norm_num

/-- Every source-table letter is positive. -/
theorem positive : ∀ j k, (triangles j k).2 = true := by
  intro j k
  fin_cases j <;> fin_cases k <;> rfl

/-- None of the fifteen source triples is a literal cube. -/
theorem noCube : ∀ j, ¬
    (triangles j 0 = triangles j 1 ∧ triangles j 1 = triangles j 2) := by
  intro j
  fin_cases j <;> decide

/-! ## Direct link checks -/

/-- The link of the published table is three-regular. -/
theorem link_regular :
    ∀ u, TriangularHodgeLayer.degree triangles u = 3 := by
  rintro ⟨i, s⟩
  fin_cases i <;> cases s <;> decide

/-- The presentation link has no multiple edge or loop. -/
theorem link_simple :
    ∀ u v, TriangularHodgeLayer.adjacencyCount triangles u v ≤ 1 := by
  rintro ⟨i, s⟩ ⟨j, t⟩
  fin_cases i <;> fin_cases j <;> cases s <;> cases t <;> decide

/-- The three line indices incident to a positive signed generator, read
directly from the cyclic corners of the source table. -/
def neighbor : Fin 15 → Fin 3 → Fin 15 :=
  ![
    ![1, 7, 13], ![6, 3, 11], ![3, 5, 13], ![12, 1, 8],
    ![0, 11, 12], ![7, 2, 11], ![0, 10, 13], ![10, 2, 8],
    ![2, 5, 14], ![4, 6, 10], ![0, 9, 14], ![3, 9, 8],
    ![1, 14, 6], ![4, 5, 12], ![4, 7, 9]
  ]

/-- Incidence matrix encoded by the three explicit neighbors in each row. -/
def incidence (x y : Fin 15) : ℕ :=
  if y = neighbor x 0 ∨ y = neighbor x 1 ∨ y = neighbor x 2 then 1 else 0

/-- The table link is the bipartite incidence graph encoded by `neighbor`.
This is the only check that unfolds the original cyclic-corner definition of
presentation-link adjacency. -/
theorem adjacency_eq_incidence : ∀ x y s t,
    TriangularHodgeLayer.adjacencyCount triangles (x, s) (y, t) =
      if s then (if t then 0 else incidence x y)
      else (if t then incidence y x else 0) := by
  intro x y s t
  fin_cases x <;> fin_cases y <;> cases s <;> cases t <;> decide

/-- Common-neighbor count of two point-side rows. -/
def rowCommon (x y : Fin 15) : ℕ :=
  ∑ a, incidence x a * incidence y a

/-- Common-neighbor count of two line-side columns. -/
def colCommon (x y : Fin 15) : ℕ :=
  ∑ a, incidence a x * incidence a y

/-- The six point-side vertices collinear with each point.  The entries are
the other two points on each of its three incident lines. -/
def pointColNeighbor : Fin 15 → Fin 6 → Fin 15 :=
  ![
    ![3, 12, 5, 14, 2, 6], ![9, 12, 2, 11, 4, 5],
    ![1, 11, 8, 13, 0, 6], ![4, 13, 0, 12, 7, 11],
    ![6, 10, 1, 5, 3, 13], ![0, 14, 7, 8, 1, 4],
    ![4, 10, 7, 9, 0, 2], ![6, 9, 5, 8, 3, 11],
    ![5, 7, 2, 13, 10, 12], ![13, 14, 1, 12, 6, 7],
    ![4, 6, 11, 14, 8, 12], ![1, 2, 10, 14, 3, 7],
    ![0, 3, 8, 10, 1, 9], ![9, 14, 2, 8, 3, 4],
    ![9, 13, 0, 5, 10, 11]
  ]

/-- Point-side collinearity adjacency. -/
def pointCol (x y : Fin 15) : ℕ :=
  ∑ k : Fin 6, if pointColNeighbor x k = y then 1 else 0

/-- The point-side association identity `N N^T = 3 I + C`. -/
theorem rowCommon_eq : ∀ x y,
    rowCommon x y = 3 * (if x = y then 1 else 0) + pointCol x y := by
  intro x y
  fin_cases x <;> fin_cases y <;> decide

/-- Distinct rows of the incidence matrix intersect in at most one entry. -/
theorem rowCommon_le_one_of_ne : ∀ x y, x ≠ y → rowCommon x y ≤ 1 := by
  intro x y hxy
  fin_cases x <;> fin_cases y <;> simp_all <;> decide

/-- Distinct columns of the incidence matrix intersect in at most one entry. -/
theorem colCommon_le_one_of_ne : ∀ x y, x ≠ y → colCommon x y ≤ 1 := by
  intro x y hxy
  fin_cases x <;> fin_cases y <;> simp_all <;> decide

/-- Two distinct signed link vertices have at most one common neighbor.  For
vertices on opposite sides the sum is zero; for same-side vertices this is
the generalized-quadrangle partial-linear-space axiom. -/
theorem commonNeighbor_le_one :
    ∀ v v', v ≠ v' →
      (∑ u, TriangularHodgeLayer.adjacencyCount triangles u v *
        TriangularHodgeLayer.adjacencyCount triangles u v') ≤ 1 := by
  rintro ⟨x, s⟩ ⟨y, t⟩ hne
  rw [Fintype.sum_prod_type]
  cases s <;> cases t
  · have hxy : x ≠ y := by
      intro h
      apply hne
      rw [h]
    simpa [adjacency_eq_incidence, colCommon] using
      colCommon_le_one_of_ne x y hxy
  · simp [adjacency_eq_incidence]
  · simp [adjacency_eq_incidence]
  · have hxy : x ≠ y := by
      intro h
      apply hne
      rw [h]
    simpa [adjacency_eq_incidence, rowCommon] using
      rowCommon_le_one_of_ne x y hxy

/-- Number of length-three link paths from positive point `x` to negative
line `y`, written as the matrix product `N N^T N`. -/
def pointLineThreePaths (x y : Fin 15) : ℕ :=
  ∑ line, ∑ point,
    incidence x line * incidence point line * incidence point y

/-- The reduced `N N^T N` expression after substituting
`N N^T = 3 I + C`. -/
def pointLineThreePathsReduced (x y : Fin 15) : ℕ :=
  ∑ point,
    (3 * (if x = point then 1 else 0) + pointCol x point) *
      incidence point y

/-- Matrix associativity and `rowCommon_eq` reduce the double path sum to a
single sum over point-side vertices. -/
theorem pointLineThreePaths_eq_reduced (x y : Fin 15) :
    pointLineThreePaths x y = pointLineThreePathsReduced x y := by
  unfold pointLineThreePaths pointLineThreePathsReduced
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro point _
  calc
    (∑ line,
        incidence x line * incidence point line * incidence point y) =
        (∑ line, incidence x line * incidence point line) *
          incidence point y := by
      rw [Finset.sum_mul]
    _ = (3 * (if x = point then 1 else 0) + pointCol x point) *
          incidence point y := by
      rw [show (∑ line, incidence x line * incidence point line) =
          rowCommon x point from rfl, rowCommon_eq]

/-- Summing a function over the collinearity row is the sum over the six
explicit collinear neighbors. -/
theorem sum_pointCol_mul (x : Fin 15) (f : Fin 15 → ℕ) :
    ∑ point, pointCol x point * f point =
      ∑ k : Fin 6, f (pointColNeighbor x k) := by
  classical
  unfold pointCol
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp

/-- The reduced path count is `3 N + C N`, with the collinearity term
evaluated on the six explicit neighbors. -/
theorem pointLineThreePathsReduced_eq_six (x y : Fin 15) :
    pointLineThreePathsReduced x y =
      3 * incidence x y +
        ∑ k : Fin 6, incidence (pointColNeighbor x k) y := by
  unfold pointLineThreePathsReduced
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  have hdiag :
      (∑ point : Fin 15,
        3 * (if x = point then 1 else 0) * incidence point y) =
          3 * incidence x y := by
    classical
    simp
  rw [hdiag, sum_pointCol_mul]

private theorem sixPaths_row_zero : ∀ y, incidence 0 y = 0 →
    (∑ k : Fin 6, incidence (pointColNeighbor 0 k) y) = 1 := by
  intro y h; fin_cases y <;> simp_all [incidence, neighbor] <;> decide
private theorem sixPaths_row_one : ∀ y, incidence 1 y = 0 →
    (∑ k : Fin 6, incidence (pointColNeighbor 1 k) y) = 1 := by
  intro y h; fin_cases y <;> simp_all [incidence, neighbor] <;> decide
private theorem sixPaths_row_two : ∀ y, incidence 2 y = 0 →
    (∑ k : Fin 6, incidence (pointColNeighbor 2 k) y) = 1 := by
  intro y h; fin_cases y <;> simp_all [incidence, neighbor] <;> decide
private theorem sixPaths_row_three : ∀ y, incidence 3 y = 0 →
    (∑ k : Fin 6, incidence (pointColNeighbor 3 k) y) = 1 := by
  intro y h; fin_cases y <;> simp_all [incidence, neighbor] <;> decide
private theorem sixPaths_row_four : ∀ y, incidence 4 y = 0 →
    (∑ k : Fin 6, incidence (pointColNeighbor 4 k) y) = 1 := by
  intro y h; fin_cases y <;> simp_all [incidence, neighbor] <;> decide
private theorem sixPaths_row_five : ∀ y, incidence 5 y = 0 →
    (∑ k : Fin 6, incidence (pointColNeighbor 5 k) y) = 1 := by
  intro y h; fin_cases y <;> simp_all [incidence, neighbor] <;> decide
private theorem sixPaths_row_six : ∀ y, incidence 6 y = 0 →
    (∑ k : Fin 6, incidence (pointColNeighbor 6 k) y) = 1 := by
  intro y h; fin_cases y <;> simp_all [incidence, neighbor] <;> decide
private theorem sixPaths_row_seven : ∀ y, incidence 7 y = 0 →
    (∑ k : Fin 6, incidence (pointColNeighbor 7 k) y) = 1 := by
  intro y h; fin_cases y <;> simp_all [incidence, neighbor] <;> decide
private theorem sixPaths_row_eight : ∀ y, incidence 8 y = 0 →
    (∑ k : Fin 6, incidence (pointColNeighbor 8 k) y) = 1 := by
  intro y h; fin_cases y <;> simp_all [incidence, neighbor] <;> decide
private theorem sixPaths_row_nine : ∀ y, incidence 9 y = 0 →
    (∑ k : Fin 6, incidence (pointColNeighbor 9 k) y) = 1 := by
  intro y h; fin_cases y <;> simp_all [incidence, neighbor] <;> decide
private theorem sixPaths_row_ten : ∀ y, incidence 10 y = 0 →
    (∑ k : Fin 6, incidence (pointColNeighbor 10 k) y) = 1 := by
  intro y h; fin_cases y <;> simp_all [incidence, neighbor] <;> decide
private theorem sixPaths_row_eleven : ∀ y, incidence 11 y = 0 →
    (∑ k : Fin 6, incidence (pointColNeighbor 11 k) y) = 1 := by
  intro y h; fin_cases y <;> simp_all [incidence, neighbor] <;> decide
private theorem sixPaths_row_twelve : ∀ y, incidence 12 y = 0 →
    (∑ k : Fin 6, incidence (pointColNeighbor 12 k) y) = 1 := by
  intro y h; fin_cases y <;> simp_all [incidence, neighbor] <;> decide
private theorem sixPaths_row_thirteen : ∀ y, incidence 13 y = 0 →
    (∑ k : Fin 6, incidence (pointColNeighbor 13 k) y) = 1 := by
  intro y h; fin_cases y <;> simp_all [incidence, neighbor] <;> decide
private theorem sixPaths_row_fourteen : ∀ y, incidence 14 y = 0 →
    (∑ k : Fin 6, incidence (pointColNeighbor 14 k) y) = 1 := by
  intro y h; fin_cases y <;> simp_all [incidence, neighbor] <;> decide

/-- The generalized-quadrangle axiom: a nonincident point and line determine
exactly one three-edge path in the incidence graph. -/
theorem pointLineThreePaths_eq_one_of_nonincident :
    ∀ x y, incidence x y = 0 → pointLineThreePaths x y = 1 := by
  intro x y hxy
  rw [pointLineThreePaths_eq_reduced,
    pointLineThreePathsReduced_eq_six, hxy, mul_zero, zero_add]
  fin_cases x
  · exact sixPaths_row_zero y hxy
  · exact sixPaths_row_one y hxy
  · exact sixPaths_row_two y hxy
  · exact sixPaths_row_three y hxy
  · exact sixPaths_row_four y hxy
  · exact sixPaths_row_five y hxy
  · exact sixPaths_row_six y hxy
  · exact sixPaths_row_seven y hxy
  · exact sixPaths_row_eight y hxy
  · exact sixPaths_row_nine y hxy
  · exact sixPaths_row_ten y hxy
  · exact sixPaths_row_eleven y hxy
  · exact sixPaths_row_twelve y hxy
  · exact sixPaths_row_thirteen y hxy
  · exact sixPaths_row_fourteen y hxy

/-- Reversing a length-three point-line path does not change its count. -/
theorem pointLineThreePaths_comm (x y : Fin 15) :
    (∑ point, ∑ line,
      incidence point x * incidence point line * incidence y line) =
        pointLineThreePaths y x := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro line _
  apply Finset.sum_congr rfl
  intro point _
  ring

/-- Between two nonadjacent link vertices there is at most one path of
length three.  This is the generalized-quadrangle axiom in incidence-graph
form and excludes embedded six-cycles. -/
theorem nonedge_threePaths_le_one :
    ∀ v v', TriangularHodgeLayer.adjacencyCount triangles v v' = 0 →
      (∑ a, ∑ b, TriangularHodgeLayer.adjacencyCount triangles v a *
        TriangularHodgeLayer.adjacencyCount triangles a b *
        TriangularHodgeLayer.adjacencyCount triangles b v') ≤ 1 := by
  rintro ⟨x, s⟩ ⟨y, t⟩ hnonedge
  cases s <;> cases t
  · simp only [Fintype.sum_prod_type]
    simp [adjacency_eq_incidence]
  · have hinc : incidence y x = 0 := by
      simpa [adjacency_eq_incidence] using hnonedge
    rw [show (∑ a, ∑ b,
        TriangularHodgeLayer.adjacencyCount triangles (x, false) a *
          TriangularHodgeLayer.adjacencyCount triangles a b *
          TriangularHodgeLayer.adjacencyCount triangles b (y, true)) =
        pointLineThreePaths y x by
      simp only [Fintype.sum_prod_type]
      simpa [adjacency_eq_incidence] using pointLineThreePaths_comm x y]
    exact (pointLineThreePaths_eq_one_of_nonincident y x hinc).le
  · have hinc : incidence x y = 0 := by
      simpa [adjacency_eq_incidence] using hnonedge
    rw [show (∑ a, ∑ b,
        TriangularHodgeLayer.adjacencyCount triangles (x, true) a *
          TriangularHodgeLayer.adjacencyCount triangles a b *
          TriangularHodgeLayer.adjacencyCount triangles b (y, false)) =
        pointLineThreePaths x y by
      simp only [Fintype.sum_prod_type]
      simp [adjacency_eq_incidence, pointLineThreePaths]]
    exact (pointLineThreePaths_eq_one_of_nonincident x y hinc).le
  · simp only [Fintype.sum_prod_type]
    simp [adjacency_eq_incidence]

/-- The published `T_1` table passes the repository's exact finite
`C(3)`--`T(8)` predicate at degree three. -/
theorem girthEightChecks : GirthEightChecks triangles 3 :=
  ⟨positive, link_regular, link_simple, commonNeighbor_le_one,
    nonedge_threePaths_le_one⟩

/-! ## Association-scheme calibration at `q = 2` -/

/-- Rational adjacency table of the thirty-vertex presentation link. -/
def adj (u v : Fin 15 × Bool) : ℚ :=
  TriangularHodgeLayer.adjacencyCount triangles u v

/-- Bipartition sign of a signed link vertex. -/
def sign (u : Fin 15 × Bool) : ℚ := if u.2 then 1 else -1

/-- The adjacency matrix is symmetric. -/
theorem adj_symm (u v : Fin 15 × Bool) : adj u v = adj v u := by
  unfold adj
  rw [TriangularHodgeLayer.adjacencyCount_comm]

/-- The sign has square one. -/
theorem sign_sq (u : Fin 15 × Bool) : sign u * sign u = 1 := by
  rcases u with ⟨i, s⟩
  cases s <;> norm_num [sign]

/-- The two parts of the link both have fifteen vertices. -/
theorem sign_sum : ∑ u : Fin 15 × Bool, sign u = 0 := by
  rw [Fintype.sum_prod_type]
  simp [sign]

/-- The square-root-free projector parameter `a = 1-gap` at the exact
normalized spectral gap `gap=1/3`. -/
theorem projector_a : (1 : ℚ) - 1 / 3 = 2 / 3 := by
  norm_num

/-- The four diagonal weights emitted by
`generate_gq_projector_ldl.py --symbolic-q 2 --gap 1/3`. -/
def projectorDiagonal : Fin 4 → ℚ :=
  ![(5 / 3 : ℚ), 2 / 3, 3 / 4, 0]

/-- All four calibration weights are nonnegative; the final spectral-block
weight is exactly zero at the true `GQ(2,2)` gap. -/
theorem projectorDiagonal_nonneg (k : Fin 4) :
    0 ≤ projectorDiagonal k := by
  fin_cases k <;> norm_num [projectorDiagonal]

/-- The exact coefficient check used by the script for the `Q^2` and `E_s`
blocks. -/
theorem projectorCoefficientCheck :
    (3 / 4 : ℚ) * ((2 / 3 : ℚ) ^ 2 + 4 / 9) + 0 = 2 / 3 ∧
      (3 / 4 : ℚ) * (-2 / 3 * (2 / 3 : ℚ)) = -1 / 3 := by
  norm_num

end GQTwoTable
end KazhdanHyp
end GroupApproximation
