import GroupApproximation.PropertyTT.MatrixElimination

/-!
# Coordinate blocks in a general linear group

The subgroup `coordinateBlock R j` consists of the invertible matrices whose
`j`-th row and column are those of the identity.  It is the intrinsic,
coordinate-free-in-rank version of `diag(GL_{n-1}(R), 1)` used in Mimura's
relative rigidity theorem.
-/

namespace GroupApproximation

variable {R ι : Type*} [Ring R] [Fintype ι] [DecidableEq ι]

/-- An invertible matrix fixes the `j`-coordinate as a direct summand. -/
def IsCoordinateBlock (j : ι) (A : (Matrix ι ι R)ˣ) : Prop :=
  (∀ c, (A : Matrix ι ι R) j c = if j = c then 1 else 0) ∧
  (∀ r, (A : Matrix ι ι R) r j = if r = j then 1 else 0)

/-- The copy of `GL` on all coordinates except `j`. -/
def coordinateBlock (R : Type*) [Ring R] (j : ι) :
    Subgroup (Matrix ι ι R)ˣ where
  carrier := {A | IsCoordinateBlock j A}
  one_mem' := by
    constructor <;> intro k <;> simp [Matrix.one_apply]
  mul_mem' := by
    intro A B hA hB
    constructor
    · intro c
      change ((A : Matrix ι ι R) * (B : Matrix ι ι R)) j c = _
      rw [Matrix.mul_apply]
      simp_rw [hA.1]
      simp
      exact hB.1 c
    · intro r
      change ((A : Matrix ι ι R) * (B : Matrix ι ι R)) r j = _
      rw [Matrix.mul_apply]
      simp_rw [hB.2]
      simp
      exact hA.2 r
  inv_mem' := by
    intro A hA
    constructor
    · intro c
      change A.inv j c = _
      have hentry := congrFun (congrFun A.val_inv j) c
      change ((A : Matrix ι ι R) * A.inv) j c = _ at hentry
      rw [Matrix.mul_apply] at hentry
      simp_rw [hA.1] at hentry
      simp only [ite_mul, one_mul, zero_mul, Fintype.sum_ite_eq,
        Matrix.one_apply] at hentry
      exact hentry
    · intro r
      change A.inv r j = _
      have hentry := congrFun (congrFun A.inv_val r) j
      change (A.inv * (A : Matrix ι ι R)) r j = _ at hentry
      rw [Matrix.mul_apply] at hentry
      simp_rw [hA.2] at hentry
      simp only [mul_ite, mul_one, mul_zero, Fintype.sum_ite_eq',
        Matrix.one_apply] at hentry
      exact hentry

@[simp] theorem mem_coordinateBlock_iff (j : ι) (A : (Matrix ι ι R)ˣ) :
    A ∈ coordinateBlock R j ↔ IsCoordinateBlock j A := Iff.rfl

/-- A root transvection lies in every coordinate block avoiding its two
indices. -/
theorem elementaryUnit_mem_coordinateBlock_of_ne
    (q i j : ι) (hij : i ≠ j) (hqi : q ≠ i) (hqj : q ≠ j) (a : R) :
    elementaryUnit i j hij a ∈ coordinateBlock R q := by
  constructor
  · intro c
    have hiq : i ≠ q := Ne.symm hqi
    change (1 + Matrix.single i j a) q c = _
    simp [Matrix.one_apply, Matrix.single, hiq]
  · intro r
    have hjq : j ≠ q := Ne.symm hqj
    change (1 + Matrix.single i j a) r q = _
    simp [Matrix.one_apply, Matrix.single, hjq]

/-! ## Clearing all coordinates except one -/

/-- The duplicate-free list of coordinates other than `j`. -/
noncomputable def otherIndices (j : ι) : List {k : ι // k ≠ j} :=
  Finset.univ.toList

theorem otherIndices_nodup (j : ι) : (otherIndices j).Nodup :=
  Finset.nodup_toList _

@[simp] theorem mem_otherIndices_values_iff (j c : ι) :
    c ∈ (otherIndices j).map
      ((↑·) : {k : ι // k ≠ j} → ι) ↔ c ≠ j := by
  constructor
  · intro hc
    obtain ⟨k, _, hkc⟩ := List.mem_map.mp hc
    subst c
    exact k.property
  · intro hc
    apply List.mem_map.mpr
    exact ⟨⟨c, hc⟩, by simp [otherIndices], rfl⟩

/-- If the distinguished diagonal entry is `1`, simultaneous right
transvections clear the rest of its row. -/
theorem rightClearFactors_clear_row (A : Matrix ι ι R) (j : ι)
    (hjj : A j j = 1) (c : ι) :
    (A * ((rightClearFactors j (fun k ↦ -A j k) (otherIndices j)).prod :
      (Matrix ι ι R)ˣ)) j c = if j = c then 1 else 0 := by
  rw [mul_rightClearFactors_apply A j (fun k ↦ -A j k)
    (otherIndices j) (otherIndices_nodup j)]
  by_cases hjc : j = c
  · subst c
    rw [if_neg (by simp), if_pos rfl, hjj]
  · rw [if_pos ((mem_otherIndices_values_iff j c).2 (Ne.symm hjc)),
      if_neg hjc, hjj]
    simp

/-- Right clearing leaves the distinguished column unchanged. -/
theorem rightClearFactors_preserve_column (A : Matrix ι ι R) (j r : ι) :
    (A * ((rightClearFactors j (fun k ↦ -A j k) (otherIndices j)).prod :
      (Matrix ι ι R)ˣ)) r j = A r j := by
  rw [mul_rightClearFactors_apply A j (fun k ↦ -A j k)
    (otherIndices j) (otherIndices_nodup j)]
  rw [if_neg (by simp)]

/-- Once the distinguished row is standard and its diagonal entry is `1`,
simultaneous left transvections clear the rest of its column while preserving
that row. -/
theorem leftClearFactors_make_coordinateBlock
    (A : (Matrix ι ι R)ˣ) (j : ι)
    (hrow : ∀ c, (A : Matrix ι ι R) j c = if j = c then 1 else 0) :
    ((leftClearFactors j (fun r ↦ -(A : Matrix ι ι R) r j)
      (otherIndices j)).prod * A) ∈ coordinateBlock R j := by
  constructor
  · intro c
    change ((((leftClearFactors j (fun r ↦
      -(A : Matrix ι ι R) r j) (otherIndices j)).prod :
        (Matrix ι ι R)ˣ) : Matrix ι ι R) *
          (A : Matrix ι ι R)) j c = _
    rw [leftClearFactors_mul_apply (A : Matrix ι ι R) j
      (fun r ↦ -(A : Matrix ι ι R) r j)
      (otherIndices j) (otherIndices_nodup j)]
    rw [if_neg (by simp)]
    exact hrow c
  · intro r
    change ((((leftClearFactors j (fun r ↦
      -(A : Matrix ι ι R) r j) (otherIndices j)).prod :
        (Matrix ι ι R)ˣ) : Matrix ι ι R) *
          (A : Matrix ι ι R)) r j = _
    rw [leftClearFactors_mul_apply (A : Matrix ι ι R) j
      (fun r ↦ -(A : Matrix ι ι R) r j)
      (otherIndices j) (otherIndices_nodup j)]
    by_cases hrj : r = j
    · subst r
      rw [if_neg (by simp), if_pos rfl, hrow j, if_pos rfl]
    · rw [if_pos ((mem_otherIndices_values_iff j r).2 hrj),
        if_neg hrj, hrow j, if_pos rfl]
      simp

/-- **One-stage strong-division elimination.**  For any two distinct
coordinates, elementary row and column operations isolate the second one as
a literal identity summand.  No stable range, commutativity, or Leavitt
presentation is used. -/
theorem exists_coordinateBlock_reduction [Nontrivial R]
    (hdiv : HasSingleSandwichDivision R)
    (A : (Matrix ι ι R)ˣ) (i j : ι) (hij : i ≠ j) :
    ∃ E F T S : (Matrix ι ι R)ˣ,
      E ∈ elementaryGroup ι R ∧ F ∈ elementaryGroup ι R ∧
      T = (rightClearFactors j
        (fun k ↦ -((E * A * F : (Matrix ι ι R)ˣ) : Matrix ι ι R) j k)
        (otherIndices j)).prod ∧
      S = (leftClearFactors j
        (fun r ↦ -((E * A * F * T : (Matrix ι ι R)ˣ) : Matrix ι ι R) r j)
        (otherIndices j)).prod ∧
      S * E * A * F * T ∈ coordinateBlock R j := by
  obtain ⟨E, F, hE, hF, hjj, _, _, _⟩ :=
    exists_five_move_pivot hdiv A i j hij
  let T := (rightClearFactors j
    (fun k ↦ -((E * A * F : (Matrix ι ι R)ˣ) : Matrix ι ι R) j k)
    (otherIndices j)).prod
  let C : (Matrix ι ι R)ˣ := E * A * F * T
  have hCrow : ∀ c, (C : Matrix ι ι R) j c =
      if j = c then 1 else 0 := by
    intro c
    dsimp [C, T]
    rw [← Units.val_mul]
    exact rightClearFactors_clear_row
      ((E * A * F : (Matrix ι ι R)ˣ) : Matrix ι ι R) j hjj c
  let S := (leftClearFactors j
    (fun r ↦ -(C : Matrix ι ι R) r j) (otherIndices j)).prod
  refine ⟨E, F, T, S, hE, hF, rfl, ?_, ?_⟩
  · rfl
  · simpa only [S, C, mul_assoc] using
      leftClearFactors_make_coordinateBlock C j hCrow

end GroupApproximation
