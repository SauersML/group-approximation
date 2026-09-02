import GroupApproximation.GGT.KazhdanHypGQEightTableFormat

set_option maxHeartbeats 800000

/-!
# Per-point verification for generated triangle tables

For a fixed point, `pointPairCheck` checks all outgoing compatible directed
pairs and `pointRowsCheck` checks cyclic compatibility of every row containing
that point.  The global local conditions follow by running `checkPoint` at
each point, so generated W(8) witnesses can emit one small kernel decision per
point instead of one reduction over all 585 points at once.  This is the
finite-table form of the row-local checks in the triangle-presentation
definition of Kangaslampi--Vdovina.
-/

namespace GroupApproximation
namespace KazhdanHyp
namespace GQEightTableFormat

open scoped BigOperators

/-! ## Local predicates -/

/-- A row contains a point in one of its three cyclic positions. -/
def rowUsesPoint {n m : ℕ} (T : Table n m) (j : Fin m) (x : Fin n) : Bool :=
  decide ((T.rows j).x = x ∨ (T.rows j).y = x ∨ (T.rows j).z = x)

/-- Exact-cover and cyclic-row checks attached to one point. -/
def pointPairCheck {n m : ℕ} (T : Table n m) (x : Fin n) : Bool :=
  allFinN n (fun y => decide
    (pairCoverCount T x y = if member T x y = true then 1 else 0))

def pointRowsCheck {n m : ℕ} (T : Table n m) (x : Fin n) : Bool :=
  allFinN m (fun j =>
    if rowUsesPoint T j x = true then
      decide (rowCompatible T (T.rows j) = true)
    else true)

/-- The Boolean fact emitted for one point of a generated table. -/
def checkPoint {n m : ℕ} (T : Table n m) (x : Fin n) : Bool :=
  pointPairCheck T x && pointRowsCheck T x

/-- Names used by the generated W(8) verifier. -/
def checkBijective {n m : ℕ} (T : Table n m) : Bool := lambdaCheck T

def checkNoConstantRows {n m : ℕ} (T : Table n m) : Bool := noCubeCheck T

def checkGirth {n m : ℕ} (T : Table n m) : Bool := girthCheckAt T 9

theorem rowUsesPoint_spec {n m : ℕ} (T : Table n m) (j : Fin m) (x : Fin n) :
    rowUsesPoint T j x = true ↔
      (T.rows j).x = x ∨ (T.rows j).y = x ∨ (T.rows j).z = x := by
  simp [rowUsesPoint]

theorem pointPairCheck_spec {n m : ℕ} (T : Table n m) (x : Fin n) :
    pointPairCheck T x = true ↔
      ∀ y, pairCoverCount T x y = if member T x y = true then 1 else 0 := by
  unfold pointPairCheck
  rw [allFinN_eq_true_iff]
  constructor
  · intro h y
    exact decide_eq_true_eq.mp (h y)
  · intro h y
    exact decide_eq_true_eq.mpr (h y)

theorem pointRowsCheck_spec {n m : ℕ} (T : Table n m) (x : Fin n) :
    pointRowsCheck T x = true ↔
      ∀ j, rowUsesPoint T j x = true →
        rowCompatible T (T.rows j) = true := by
  unfold pointRowsCheck
  rw [allFinN_eq_true_iff]
  constructor
  · intro h j hj
    have hj' := h j
    simp [hj] at hj'
    exact hj'
  · intro h j
    by_cases hj : rowUsesPoint T j x = true
    · simp [hj, decide_eq_true_eq.mpr (h j hj)]
    · simp [hj]

theorem checkPoint_spec {n m : ℕ} (T : Table n m) (x : Fin n) :
    checkPoint T x = true ↔
      (∀ y, pairCoverCount T x y = if member T x y = true then 1 else 0) ∧
      (∀ j, rowUsesPoint T j x = true →
        rowCompatible T (T.rows j) = true) := by
  unfold checkPoint
  rw [Bool.and_eq_true, pointPairCheck_spec, pointRowsCheck_spec]

/-! ## Assembly of the local checks -/

theorem pairCoverCheck_of_checkPoints {n m : ℕ} (T : Table n m)
    (hpoints : ∀ x, checkPoint T x = true) :
    pairCoverCheck T = true := by
  unfold pairCoverCheck
  apply (allFinN_eq_true_iff _ _).mpr
  intro x
  apply (allFinN_eq_true_iff _ _).mpr
  intro y
  have hx := (checkPoint_spec T x).mp (hpoints x)
  exact decide_eq_true_eq.mpr (hx.1 y)

theorem rowCompatibilityCheck_of_checkPoints {n m : ℕ} (T : Table n m)
    (hpoints : ∀ x, checkPoint T x = true) :
    rowCompatibilityCheck T = true := by
  unfold rowCompatibilityCheck
  apply (allFinN_eq_true_iff _ _).mpr
  intro j
  have hx := (checkPoint_spec T (T.rows j).x).mp (hpoints (T.rows j).x)
  have huse : rowUsesPoint T j (T.rows j).x = true := by
    simp [rowUsesPoint]
  exact (hx.2 j huse)

/-! ## Degree-nine W(8) assembly -/

theorem checkTable_true_of_checkPoints {m : ℕ} (T : Table 585 m)
    (hpoints : ∀ x, checkPoint T x = true)
    (hbij : checkBijective T = true)
    (hno : checkNoConstantRows T = true)
    (hgirth : checkGirth T = true) :
    checkTable T = true := by
  have hp : positiveCardinalityCheck T = true := by
    simp [positiveCardinalityCheck]
  have hl : lambdaCheck T = true := hbij
  have hr : rowCompatibilityCheck T = true :=
    rowCompatibilityCheck_of_checkPoints T hpoints
  have hc : pairCoverCheck T = true :=
    pairCoverCheck_of_checkPoints T hpoints
  have hn : noCubeCheck T = true := hno
  have hlocal : localCheck T = true := by
    rw [localCheck, hp, hl, hr, hc, hn]
    rfl
  have htable : checkTableAt T 9 = true := by
    have hg : girthCheckAt T 9 = true := by
      simpa [checkGirth] using hgirth
    rw [checkTableAt, hlocal, hg]
    rfl
  exact htable

theorem checkTable_of_checkPoints {m : ℕ} (T : Table 585 m)
    (hpoints : ∀ x, checkPoint T x = true)
    (hbij : checkBijective T = true)
    (hno : checkNoConstantRows T = true)
    (hgirth : checkGirth T = true) :
    GirthEightChecks (triangles T) 9 := by
  apply checkTable_true_girth T
  exact checkTable_true_of_checkPoints T hpoints hbij hno hgirth

/-! ## q=2 generator calibration and a Fin(585) cost sample -/

theorem qTwoData_all_checkPoint :
    ∀ x, checkPoint qTwoData x = true := by
  intro x
  fin_cases x <;> decide

/-- A fabricated W(8)-sized table with no rows.  One per-point decision still
has 585 pair positions, so this theorem measures the intended single-point
kernel reduction without constructing a 585 by 1755 witness. -/
def syntheticW8OnePoint : Table 585 0 := {
  incident := fun _ _ => false
  lambda := fun _ => 0
  rows := fun j => nomatch j }

theorem syntheticW8OnePoint_checkPoint :
    checkPoint syntheticW8OnePoint 0 = true := by
  set_option maxRecDepth 4096 in decide

end GQEightTableFormat
end KazhdanHyp
end GroupApproximation
