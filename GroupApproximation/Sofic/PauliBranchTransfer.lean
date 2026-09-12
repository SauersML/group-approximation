import GroupApproximation.Sofic.ExactInvolutionCut

/-!
# The exact two-arrow Pauli branch packet

The raw involution exchanges the two halves of one Pauli cut while preserving
a second cut.  After transport by the comb unitary, the two resulting range
projections are orthogonal and fill the transported second cut.  These are the
exact operator identities behind the final multiplication-to-support gate in
the Leavitt-atlas program.
-/

namespace GroupApproximation

open Matrix

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- The common initial carrier of the two raw branch arrows. -/
def pauliBranchInitial (P Q : Matrix Y Y ℂ) : Matrix Y Y ℂ := P * Q

/-- The first transported branch arrow. -/
def pauliBranchArrowZero (U P Q : Matrix Y Y ℂ) : Matrix Y Y ℂ :=
  Uᴴ * (P * Q)

/-- The second transported branch arrow. -/
def pauliBranchArrowOne (U R P Q : Matrix Y Y ℂ) : Matrix Y Y ℂ :=
  Uᴴ * R * (P * Q)

/-- The first branch range after transport by `U`. -/
def pauliBranchRangeZero (U P Q : Matrix Y Y ℂ) : Matrix Y Y ℂ :=
  Uᴴ * (P * Q) * U

/-- The second branch range: first flip the Pauli half by `R`, then transport
by `U`. -/
def pauliBranchRangeOne (U R P Q : Matrix Y Y ℂ) : Matrix Y Y ℂ :=
  Uᴴ * (R * (P * Q) * R) * U

omit [DecidableEq Y] in theorem pauliBranchInitial_star (P Q : Matrix Y Y ℂ)
    (hPstar : Pᴴ = P) (hQstar : Qᴴ = Q) (hPQ : P * Q = Q * P) :
    (pauliBranchInitial P Q)ᴴ = pauliBranchInitial P Q := by
  unfold pauliBranchInitial
  rw [Matrix.conjTranspose_mul, hPstar, hQstar, hPQ]

omit [DecidableEq Y] in theorem pauliBranchInitial_idem (P Q : Matrix Y Y ℂ)
    (hPid : P * P = P) (hQid : Q * Q = Q) (hPQ : P * Q = Q * P) :
    pauliBranchInitial P Q * pauliBranchInitial P Q =
      pauliBranchInitial P Q := by
  unfold pauliBranchInitial
  calc
    (P * Q) * (P * Q) = P * (Q * P) * Q := by noncomm_ring
    _ = P * (P * Q) * Q := by rw [← hPQ]
    _ = (P * P) * (Q * Q) := by noncomm_ring
    _ = P * Q := by rw [hPid, hQid]

/-- Both transported arrows have the same initial projection `P Q`. -/
theorem pauliBranchArrows_same_initial (U R P Q : Matrix Y Y ℂ)
    (hU : U * Uᴴ = 1) (hRstar : Rᴴ = R) (hRsq : R * R = 1)
    (hPstar : Pᴴ = P) (hQstar : Qᴴ = Q)
    (hPid : P * P = P) (hQid : Q * Q = Q) (hPQ : P * Q = Q * P) :
    (pauliBranchArrowZero U P Q)ᴴ * pauliBranchArrowZero U P Q =
        pauliBranchInitial P Q ∧
      (pauliBranchArrowOne U R P Q)ᴴ * pauliBranchArrowOne U R P Q =
        pauliBranchInitial P Q := by
  have hEstar : (P * Q)ᴴ = P * Q := by
    simpa [pauliBranchInitial] using
      pauliBranchInitial_star P Q hPstar hQstar hPQ
  have hEid : (P * Q) * (P * Q) = P * Q := by
    simpa [pauliBranchInitial] using
      pauliBranchInitial_idem P Q hPid hQid hPQ
  constructor
  · unfold pauliBranchArrowZero pauliBranchInitial
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hEstar]
    calc
      (P * Q) * U * (Uᴴ * (P * Q)) =
          (P * Q) * (U * Uᴴ) * (P * Q) := by noncomm_ring
      _ = P * Q := by rw [hU, Matrix.mul_one, hEid]
  · unfold pauliBranchArrowOne pauliBranchInitial
    have hUR : (Uᴴ * R)ᴴ = R * U := by
      rw [Matrix.conjTranspose_mul, hRstar,
        Matrix.conjTranspose_conjTranspose]
    rw [Matrix.conjTranspose_mul, hEstar, hUR]
    calc
      (P * Q) * (R * U) * (Uᴴ * R * (P * Q)) =
          (P * Q) * R * (U * Uᴴ) * R * (P * Q) := by noncomm_ring
      _ = (P * Q) * (R * R) * (P * Q) := by
        rw [hU, Matrix.mul_one]
        noncomm_ring
      _ = P * Q := by rw [hRsq, Matrix.mul_one, hEid]

omit [DecidableEq Y] in
/-- The named range projections are exactly `T_i T_i*` for the two branch
arrows. -/
theorem pauliBranchArrows_ranges
    (U R P Q : Matrix Y Y ℂ)
    (hRstar : Rᴴ = R) (hPstar : Pᴴ = P) (hQstar : Qᴴ = Q)
    (hPid : P * P = P) (hQid : Q * Q = Q) (hPQ : P * Q = Q * P) :
    pauliBranchArrowZero U P Q * (pauliBranchArrowZero U P Q)ᴴ =
        pauliBranchRangeZero U P Q ∧
      pauliBranchArrowOne U R P Q * (pauliBranchArrowOne U R P Q)ᴴ =
        pauliBranchRangeOne U R P Q := by
  have hEstar : (P * Q)ᴴ = P * Q := by
    simpa [pauliBranchInitial] using
      pauliBranchInitial_star P Q hPstar hQstar hPQ
  have hEid : (P * Q) * (P * Q) = P * Q := by
    simpa [pauliBranchInitial] using
      pauliBranchInitial_idem P Q hPid hQid hPQ
  have hUR : (Uᴴ * R)ᴴ = R * U := by
    rw [Matrix.conjTranspose_mul, hRstar,
      Matrix.conjTranspose_conjTranspose]
  constructor
  · unfold pauliBranchArrowZero pauliBranchRangeZero
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hEstar]
    calc
      (Uᴴ * (P * Q)) * ((P * Q) * U) =
          Uᴴ * ((P * Q) * (P * Q)) * U := by noncomm_ring
      _ = Uᴴ * (P * Q) * U := by rw [hEid]
  · unfold pauliBranchArrowOne pauliBranchRangeOne
    rw [Matrix.conjTranspose_mul, hEstar, hUR]
    calc
      (Uᴴ * R * (P * Q)) * ((P * Q) * (R * U)) =
          Uᴴ * R * ((P * Q) * (P * Q)) * R * U := by noncomm_ring
      _ = Uᴴ * (R * (P * Q) * R) * U := by rw [hEid]; noncomm_ring

/-- If `R` flips `P` and preserves `Q`, it carries their joint cut to the
complementary `P`-half inside `Q`. -/
theorem pauli_conj_joint_eq_complement (R P Q : Matrix Y Y ℂ)
    (hRsq : R * R = 1) (hRQ : R * Q = Q * R)
    (hflip : R * P * R = 1 - P) :
    R * (P * Q) * R = (1 - P) * Q := by
  have hRQR : R * Q * R = Q := by
    calc
      R * Q * R = (Q * R) * R := by rw [hRQ]
      _ = Q * (R * R) := by rw [mul_assoc]
      _ = Q := by rw [hRsq, Matrix.mul_one]
  calc
    R * (P * Q) * R = R * P * Q * R := by noncomm_ring
    _ = R * P * (R * R) * Q * R := by rw [hRsq, Matrix.mul_one]
    _ = (R * P * R) * (R * Q * R) := by noncomm_ring
    _ = (1 - P) * Q := by rw [hflip, hRQR]

/-- The two raw Pauli halves fill exactly the preserved carrier `Q`. -/
theorem pauli_joint_add_conj_eq_right (R P Q : Matrix Y Y ℂ)
    (hRsq : R * R = 1) (hRQ : R * Q = Q * R)
    (hflip : R * P * R = 1 - P) :
    P * Q + R * (P * Q) * R = Q := by
  rw [pauli_conj_joint_eq_complement R P Q hRsq hRQ hflip]
  noncomm_ring

/-- Commuting projections make the two Pauli halves orthogonal. -/
theorem pauli_joint_mul_conj_eq_zero (R P Q : Matrix Y Y ℂ)
    (hPid : P * P = P) (hPQ : P * Q = Q * P)
    (hRsq : R * R = 1) (hRQ : R * Q = Q * R)
    (hflip : R * P * R = 1 - P) :
    (P * Q) * (R * (P * Q) * R) = 0 := by
  rw [pauli_conj_joint_eq_complement R P Q hRsq hRQ hflip]
  have hQcomp : Q * (1 - P) = (1 - P) * Q := by
    calc
      Q * (1 - P) = Q - Q * P := by noncomm_ring
      _ = Q - P * Q := by rw [hPQ]
      _ = (1 - P) * Q := by noncomm_ring
  calc
    (P * Q) * ((1 - P) * Q) = P * (Q * (1 - P)) * Q := by
      noncomm_ring
    _ = P * ((1 - P) * Q) * Q := by rw [hQcomp]
    _ = (P * (1 - P)) * (Q * Q) := by noncomm_ring
    _ = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, hPid, sub_self,
      Matrix.zero_mul]

/-- After comb transport, the two branch ranges fill exactly the transported
`Q` carrier. -/
theorem pauliBranchRange_add (U R P Q : Matrix Y Y ℂ)
    (hRsq : R * R = 1) (hRQ : R * Q = Q * R)
    (hflip : R * P * R = 1 - P) :
    pauliBranchRangeZero U P Q + pauliBranchRangeOne U R P Q =
      Uᴴ * Q * U := by
  unfold pauliBranchRangeZero pauliBranchRangeOne
  calc
    Uᴴ * (P * Q) * U + Uᴴ * (R * (P * Q) * R) * U =
        Uᴴ * (P * Q + R * (P * Q) * R) * U := by noncomm_ring
    _ = Uᴴ * Q * U := by
      rw [pauli_joint_add_conj_eq_right R P Q hRsq hRQ hflip]

/-- Unitary transport preserves the orthogonality of the two branch ranges. -/
theorem pauliBranchRange_mul_eq_zero (U R P Q : Matrix Y Y ℂ)
    (hU : U * Uᴴ = 1) (hPid : P * P = P) (hPQ : P * Q = Q * P)
    (hRsq : R * R = 1) (hRQ : R * Q = Q * R)
    (hflip : R * P * R = 1 - P) :
    pauliBranchRangeZero U P Q * pauliBranchRangeOne U R P Q = 0 := by
  unfold pauliBranchRangeZero pauliBranchRangeOne
  calc
    (Uᴴ * (P * Q) * U) * (Uᴴ * (R * (P * Q) * R) * U) =
        Uᴴ * (P * Q) * (U * Uᴴ) * (R * (P * Q) * R) * U := by
          noncomm_ring
    _ = Uᴴ * ((P * Q) * (R * (P * Q) * R)) * U := by
      rw [hU, Matrix.mul_one]
      noncomm_ring
    _ = 0 := by
      rw [pauli_joint_mul_conj_eq_zero R P Q hPid hPQ hRsq hRQ hflip,
        Matrix.mul_zero, Matrix.zero_mul]

/-- A larger-rank range cannot be contained in a smaller-rank carrier.  This
is the finite-coordinate endpoint of the Pauli branch packet. -/
theorem one_sub_mul_ne_zero_of_rank_lt (E F : Matrix Y Y ℂ)
    (hrank : E.rank < F.rank) : (1 - E) * F ≠ 0 := by
  intro hzero
  have hF : F = E * F := by
    calc
      F = 1 * F := by rw [Matrix.one_mul]
      _ = (E + (1 - E)) * F := by congr 1; module
      _ = E * F + (1 - E) * F := by rw [Matrix.add_mul]
      _ = E * F := by rw [hzero, add_zero]
  have hle : F.rank ≤ E.rank := by
    rw [hF]
    exact Matrix.rank_mul_le_left E F
  exact (Nat.not_le_of_lt hrank) hle

end GroupApproximation
