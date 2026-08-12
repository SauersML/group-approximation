import GroupApproximation.PropertyTT.CoordinateBlocks
import GroupApproximation.Leavitt.ElementaryStabilization

/-!
# Stabilization is exactly a coordinate block

For a one-dimensional complementary summand, block-diagonal stabilization
identifies the smaller general linear group with the intrinsic coordinate
block fixing that summand.  The inverse is constructed by taking the
upper-left block, and its inverse laws are proved from the full matrix inverse
laws.  This is purely algebraic and works over every unital ring.
-/

namespace GroupApproximation

variable {R ι : Type*} [Ring R] [Fintype ι] [DecidableEq ι]

private theorem coordinateBlock_sum_eq_fromBlocks
    (u : (Matrix (ι ⊕ Unit) (ι ⊕ Unit) R)ˣ)
    (hu : u ∈ coordinateBlock R (Sum.inr ())) :
    (↑u : Matrix (ι ⊕ Unit) (ι ⊕ Unit) R) =
      Matrix.fromBlocks
        (Matrix.toBlocks₁₁ (↑u : Matrix (ι ⊕ Unit) (ι ⊕ Unit) R)) 0 0 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · rfl
  · simpa [IsCoordinateBlock] using hu.2 (Sum.inl i)
  · simpa [IsCoordinateBlock] using hu.1 (Sum.inl j)
  · simpa [IsCoordinateBlock, Matrix.one_apply] using hu.1 (Sum.inr j)

/-- Restrict a coordinate-block unit to its non-fixed summand. -/
noncomputable def coordinateBlockRestriction
    (u : coordinateBlock R (Sum.inr () : ι ⊕ Unit)) :
    (Matrix ι ι R)ˣ where
  val := Matrix.toBlocks₁₁
    (↑(u : (Matrix (ι ⊕ Unit) (ι ⊕ Unit) R)ˣ) :
      Matrix (ι ⊕ Unit) (ι ⊕ Unit) R)
  inv := Matrix.toBlocks₁₁
    (↑((u : (Matrix (ι ⊕ Unit) (ι ⊕ Unit) R)ˣ)⁻¹) :
      Matrix (ι ⊕ Unit) (ι ⊕ Unit) R)
  val_inv := by
    have hu := u.property
    have huinv := (coordinateBlock R (Sum.inr () : ι ⊕ Unit)).inv_mem hu
    have h := congrArg Matrix.toBlocks₁₁
      ((u : (Matrix (ι ⊕ Unit) (ι ⊕ Unit) R)ˣ).val_inv)
    change Matrix.toBlocks₁₁
      ((↑(u : (Matrix (ι ⊕ Unit) (ι ⊕ Unit) R)ˣ) :
          Matrix (ι ⊕ Unit) (ι ⊕ Unit) R) *
        (↑((u : (Matrix (ι ⊕ Unit) (ι ⊕ Unit) R)ˣ)⁻¹) :
          Matrix (ι ⊕ Unit) (ι ⊕ Unit) R)) =
        Matrix.toBlocks₁₁ 1 at h
    rw [coordinateBlock_sum_eq_fromBlocks (u :=
          (u : (Matrix (ι ⊕ Unit) (ι ⊕ Unit) R)ˣ)) hu,
      coordinateBlock_sum_eq_fromBlocks (u :=
          (u : (Matrix (ι ⊕ Unit) (ι ⊕ Unit) R)ˣ)⁻¹) huinv,
      Matrix.fromBlocks_multiply] at h
    have hone : Matrix.toBlocks₁₁
        (1 : Matrix (ι ⊕ Unit) (ι ⊕ Unit) R) =
        (1 : Matrix ι ι R) := by
      ext i j
      change (if (Sum.inl i : ι ⊕ Unit) = Sum.inl j then 1 else 0) =
        if i = j then 1 else 0
      simp
    rw [hone] at h
    simpa only [Matrix.toBlocks_fromBlocks₁₁, Matrix.zero_mul,
      Matrix.mul_zero, add_zero, Matrix.one_mul] using h
  inv_val := by
    have hu := u.property
    have huinv := (coordinateBlock R (Sum.inr () : ι ⊕ Unit)).inv_mem hu
    have h := congrArg Matrix.toBlocks₁₁
      ((u : (Matrix (ι ⊕ Unit) (ι ⊕ Unit) R)ˣ).inv_val)
    change Matrix.toBlocks₁₁
      ((↑((u : (Matrix (ι ⊕ Unit) (ι ⊕ Unit) R)ˣ)⁻¹) :
          Matrix (ι ⊕ Unit) (ι ⊕ Unit) R) *
        (↑(u : (Matrix (ι ⊕ Unit) (ι ⊕ Unit) R)ˣ) :
          Matrix (ι ⊕ Unit) (ι ⊕ Unit) R)) =
        Matrix.toBlocks₁₁ 1 at h
    rw [coordinateBlock_sum_eq_fromBlocks (u :=
          (u : (Matrix (ι ⊕ Unit) (ι ⊕ Unit) R)ˣ)⁻¹) huinv,
      coordinateBlock_sum_eq_fromBlocks (u :=
          (u : (Matrix (ι ⊕ Unit) (ι ⊕ Unit) R)ˣ)) hu,
      Matrix.fromBlocks_multiply] at h
    have hone : Matrix.toBlocks₁₁
        (1 : Matrix (ι ⊕ Unit) (ι ⊕ Unit) R) =
        (1 : Matrix ι ι R) := by
      ext i j
      change (if (Sum.inl i : ι ⊕ Unit) = Sum.inl j then 1 else 0) =
        if i = j then 1 else 0
      simp
    rw [hone] at h
    simpa only [Matrix.toBlocks_fromBlocks₁₁, Matrix.zero_mul,
      Matrix.mul_zero, add_zero, Matrix.one_mul] using h

theorem stabilizeUnit_coordinateBlockRestriction
    (u : coordinateBlock R (Sum.inr () : ι ⊕ Unit)) :
    stabilizeUnit (coordinateBlockRestriction u) =
      (u : (Matrix (ι ⊕ Unit) (ι ⊕ Unit) R)ˣ) := by
  apply Units.ext
  exact (coordinateBlock_sum_eq_fromBlocks
    (u := (u : (Matrix (ι ⊕ Unit) (ι ⊕ Unit) R)ˣ)) u.property).symm

/-- The range of one-coordinate stabilization is precisely the coordinate
block fixing the complementary coordinate. -/
theorem range_stabilizeUnit_eq_coordinateBlock :
    MonoidHom.range (stabilizeUnit (R := R) (ι := ι) (κ := Unit)) =
      coordinateBlock R (Sum.inr ()) := by
  ext u
  constructor
  · rintro ⟨v, rfl⟩
    constructor
    · intro c
      rcases c with c | c
      · rfl
      · rfl
    · intro r
      rcases r with r | r
      · rfl
      · rfl
  · intro hu
    let u' : coordinateBlock R (Sum.inr () : ι ⊕ Unit) := ⟨u, hu⟩
    exact ⟨coordinateBlockRestriction u',
      stabilizeUnit_coordinateBlockRestriction u'⟩

variable {kappa : Type*} [Fintype kappa] [DecidableEq kappa]

/-- Reindexing carries a coordinate block to the coordinate block at the
reindexed distinguished coordinate. -/
theorem coordinateBlock_map_reindex (e : ι ≃ kappa) (j : ι) :
    (coordinateBlock R j).map
        (elementaryReindexUnitEquiv (R := R) e).toMonoidHom =
      coordinateBlock R (e j) := by
  ext u
  constructor
  · rintro ⟨v, hv, rfl⟩
    constructor
    · intro c
      change (Matrix.reindexRingEquiv R e)
          (↑v : Matrix ι ι R) (e j) c = _
      rw [Matrix.coe_reindexRingEquiv]
      simpa only [Matrix.reindex_apply, Matrix.submatrix_apply,
        e.symm_apply_apply,
        e.apply_eq_iff_eq_symm_apply] using hv.1 (e.symm c)
    · intro r
      change (Matrix.reindexRingEquiv R e)
          (↑v : Matrix ι ι R) r (e j) = _
      rw [Matrix.coe_reindexRingEquiv]
      simpa only [Matrix.reindex_apply, Matrix.submatrix_apply,
        e.symm_apply_apply, e.symm_apply_eq] using hv.2 (e.symm r)
  · intro hu
    let v : (Matrix ι ι R)ˣ :=
      elementaryReindexUnitEquiv (R := R) e.symm u
    have hv : v ∈ coordinateBlock R j := by
      constructor
      · intro c
        change (Matrix.reindexRingEquiv R e.symm)
            (↑u : Matrix kappa kappa R) j c = _
        rw [Matrix.coe_reindexRingEquiv]
        simpa [Matrix.reindex_apply] using hu.1 (e c)
      · intro r
        change (Matrix.reindexRingEquiv R e.symm)
            (↑u : Matrix kappa kappa R) r j = _
        rw [Matrix.coe_reindexRingEquiv]
        simpa [Matrix.reindex_apply] using hu.2 (e r)
    refine ⟨v, hv, ?_⟩
    exact (elementaryReindexUnitEquiv (R := R) e).apply_symm_apply u

/-- Stabilize by one coordinate and then reindex: its range is exactly the
coordinate block at the image of the new coordinate. -/
theorem range_reindexedStabilize_eq_coordinateBlock
    (e : (ι ⊕ Unit) ≃ kappa) :
    MonoidHom.range
        ((elementaryReindexUnitEquiv (R := R) e).toMonoidHom.comp
          (stabilizeUnit (R := R) (ι := ι) (κ := Unit))) =
      coordinateBlock R (e (Sum.inr ())) := by
  rw [MonoidHom.range_comp, range_stabilizeUnit_eq_coordinateBlock,
    coordinateBlock_map_reindex]

end GroupApproximation
