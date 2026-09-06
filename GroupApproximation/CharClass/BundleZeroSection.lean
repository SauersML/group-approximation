import GroupApproximation.CharClass.BundleLocal
import Mathlib.Topology.Homotopy.Equiv

/-!
# Complex vector bundles in the projection model, VIII: the zero section

The half of the decomposition `P(p ⊕ 1) = E(p) ⊔ P(p)` that
`BundleChart.lean` does not carry.  `BundleChart` cuts `P(p ⊕ 1)` along the
*hyperplane at infinity* `P(p)`, whose complement is the affine chart `E(p)`.
This file cuts it along the *zero section* instead: the single point

    Q∞ = rankOneProj (Sum.elim 0 1)

of each fibre, the line spanned by the last coordinate, which is the image of
`E(p)`'s zero section under the chart.  Its complement deformation retracts onto
`P(p)`, and that retraction is what turns the Mayer-Vietoris of
`P(L ⊕ 1) = E(L) ∪ (P(L⊕1) ∖ Z)` into the Gysin sequence of `S(L)`.

## Everything is one matrix identity

The retraction is `z ↦ conjNormalize blockProj z`, where `blockProj` is the
`ι`-row selection `Matrix ι (ι ⊕ Unit) ℂ`, i.e. the adjoint of the inclusion
isometry `ℂ^ι ↪ ℂ^ι ⊕ ℂ`.  Since `conjNormalize a (rankOneProj w)` is
`lineOf (a *ᵥ w)` and `blockProj *ᵥ w = w ∘ Sum.inl`, the retraction is
`[v : λ] ↦ [v : 0]` in coordinates, and the deformation is
`[v : λ] ↦ [v : tλ]`, i.e. `conjNormalize (lastScale t)` for the diagonal
`lastScale t = diag(1, t)`.

`blockProj` is **not invertible** and **not square**, so
`BundleLocal.conjNormalize_mem_projFibreSet` does not apply: its `IsUnit a.det`
hypothesis is used only to produce `a *ᵥ u ≠ 0`.  The generalization
`conjNormalize_mem_projFibreSet'` below takes that nonvanishing as the
hypothesis instead, in the form `(a * r * aᴴ).trace ≠ 0`, which is exactly the
open condition cutting out the complement of the zero section, and which at
`t = 0` is still satisfied.  That one change is what makes the whole file work.

## Manuscript status

Machinery.  Certifies no manuscript step on its own.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open scoped Matrix
open GroupApproximation.STW59
open unitInterval

namespace Bundle

section ZeroSection

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ### The generalized conjugation lemma -/

/-- **A rank-one projection of a fibre is moved by any matrix that does not kill
it.**  This is `BundleLocal.conjNormalize_mem_projFibreSet` with the
invertibility hypothesis replaced by the nonvanishing it was only ever used to
produce, and with `a` allowed to be rectangular.  The fixed-point hypothesis is
stated on vectors rather than as `a * q = q' * a`, because the target
projection is often `1`, for which it is vacuous. -/
theorem conjNormalize_mem_projFibreSet' {κ : Type} [Fintype κ] [DecidableEq κ]
    {a : Matrix κ ι ℂ}
    {q : Matrix ι ι ℂ} {q' : Matrix κ κ ℂ}
    (hfix : ∀ u : ι → ℂ, q *ᵥ u = u → q' *ᵥ (a *ᵥ u) = a *ᵥ u)
    {r : Matrix ι ι ℂ} (hr : r ∈ projFibreSet q) (hne : (a * r * aᴴ).trace ≠ 0) :
    conjNormalize a r ∈ projFibreSet q' := by
  obtain ⟨u, hu, hru, hqu⟩ := exists_unitVector_of_mem_projFibreSet hr
  have hau : a *ᵥ u ≠ 0 := by
    rw [hru] at hne
    exact (trace_conj_ne_zero_iff a u).mp hne
  rw [hru, conjNormalize_rankOneProj]
  exact lineOf_mem_projFibreSet hau (hfix u hqu)

/-! ### The row selection `ℂ^ι ⊕ ℂ → ℂ^ι` -/

/-- The adjoint of the inclusion isometry `ℂ^ι ↪ ℂ^ι ⊕ ℂ`: selection of the
`ι`-rows. -/
def blockProj (ι : Type) [Fintype ι] [DecidableEq ι] : Matrix ι (ι ⊕ Unit) ℂ :=
  Matrix.of fun i s =>
    Sum.elim (fun i' : ι => if i = i' then (1 : ℂ) else 0) (fun _ : Unit => (0 : ℂ)) s

@[simp]
theorem blockProj_inl (i i' : ι) :
    blockProj ι i (Sum.inl i') = if i = i' then (1 : ℂ) else 0 := rfl

@[simp]
theorem blockProj_inr (i : ι) (u : Unit) : blockProj ι i (Sum.inr u) = (0 : ℂ) := rfl

theorem blockProj_conjTranspose_apply (s : ι ⊕ Unit) (i : ι) :
    (blockProj ι)ᴴ s i = blockProj ι i s := by
  rw [Matrix.conjTranspose_apply]
  cases s with
  | inl i' =>
      rw [blockProj_inl]
      by_cases h : i = i' <;> simp [h]
  | inr u => simp

/-- The selection really selects: `blockProj *ᵥ w` is the `ι`-part of `w`. -/
theorem blockProj_mulVec (w : ι ⊕ Unit → ℂ) : blockProj ι *ᵥ w = w ∘ Sum.inl := by
  funext i
  rw [Matrix.mulVec_apply_eq_sum, Fintype.sum_sum_type]
  simp

theorem blockProj_mul (M : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ) (i : ι) (s : ι ⊕ Unit) :
    (blockProj ι * M) i s = M (Sum.inl i) s := by
  rw [Matrix.mul_apply, Fintype.sum_sum_type]
  simp

theorem mul_blockProj_conjTranspose (M : Matrix ι (ι ⊕ Unit) ℂ) (i i' : ι) :
    (M * (blockProj ι)ᴴ) i i' = M i (Sum.inl i') := by
  rw [Matrix.mul_apply, Fintype.sum_sum_type]
  simp

theorem blockProj_conj_apply (M : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ) (i i' : ι) :
    (blockProj ι * M * (blockProj ι)ᴴ) i i' = M (Sum.inl i) (Sum.inl i') := by
  rw [mul_blockProj_conjTranspose, blockProj_mul]

theorem blockProj_conj_inclMat (q : Matrix ι ι ℂ) :
    blockProj ι * inclMat q * (blockProj ι)ᴴ = q := by
  ext i i'
  rw [blockProj_conj_apply, inclMat_apply_inl_inl]

/-- The selection intertwines `p ⊕ 1` with `p`. -/
theorem blockProj_fix (p : Bundle X ι) (x : X) (u : ι ⊕ Unit → ℂ)
    (hu : p.plusOne x *ᵥ u = u) :
    p x *ᵥ (blockProj ι *ᵥ u) = blockProj ι *ᵥ u := by
  rw [blockProj_mulVec]
  exact (mem_plusOne_fibre_iff p x u).mp hu

/-! ### The `ι`-block of a matrix, and of a line -/

omit [Fintype ι] [DecidableEq ι] in
theorem inclMat_smul (c : ℂ) (q : Matrix ι ι ℂ) : inclMat (c • q) = c • inclMat q := by
  ext s s'
  cases s with
  | inl i =>
      cases s' with
      | inl j => rfl
      | inr u => simp [inclMat_def]
  | inr u =>
      cases s' with
      | inl j => simp [inclMat_def]
      | inr u' => simp [inclMat_def]

omit [Fintype ι] [DecidableEq ι] in
theorem rankOneProj_sum_elim_zero (v : ι → ℂ) :
    rankOneProj (Sum.elim v (0 : Unit → ℂ)) = inclMat (rankOneProj v) := by
  ext s s'
  cases s with
  | inl i =>
      cases s' with
      | inl j => rfl
      | inr u => simp [rankOneProj_apply, inclMat_def]
  | inr u =>
      cases s' with
      | inl j => simp [rankOneProj_apply, inclMat_def]
      | inr u' => simp [rankOneProj_apply]

omit [DecidableEq ι] in
theorem eucNormSq_sum_elim_zero (v : ι → ℂ) :
    eucNormSq (Sum.elim v (0 : Unit → ℂ)) = eucNormSq v := by
  rw [eucNormSq_sum_type]
  have h0 : (Sum.elim v (0 : Unit → ℂ)) ∘ Sum.inr = (0 : Unit → ℂ) := rfl
  have hl : (Sum.elim v (0 : Unit → ℂ)) ∘ Sum.inl = v := rfl
  rw [h0, hl, eucNormSq_eq_zero_iff.mpr rfl, add_zero]

omit [DecidableEq ι] in
theorem lineOf_sum_elim_zero (v : ι → ℂ) :
    lineOf (Sum.elim v (0 : Unit → ℂ)) = inclMat (lineOf v) := by
  rw [lineOf_def, lineOf_def, eucNormSq_sum_elim_zero, rankOneProj_sum_elim_zero, inclMat_smul]

/-! ### The point at infinity and the zero section -/

/-- `Q∞`: the line spanned by the last coordinate.  It is the image of the zero
section of `E(p)` under the affine chart. -/
noncomputable def infPoint (ι : Type) [Fintype ι] : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ :=
  rankOneProj (Sum.elim (0 : ι → ℂ) (fun _ : Unit => (1 : ℂ)))

omit [Fintype ι] [DecidableEq ι] in
theorem infVec_comp_inl :
    (Sum.elim (0 : ι → ℂ) (fun _ : Unit => (1 : ℂ))) ∘ Sum.inl = (0 : ι → ℂ) := rfl

omit [DecidableEq ι] in
theorem infVec_mem_unitVectors :
    (Sum.elim (0 : ι → ℂ) (fun _ : Unit => (1 : ℂ))) ∈ unitVectors (ι ⊕ Unit) := by
  rw [mem_unitVectors_iff_eucNormSq, eucNormSq_sum_type, infVec_comp_inl,
    eucNormSq_eq_zero_iff.mpr rfl, zero_add, eucNormSq_def]
  simp

omit [DecidableEq ι] in
theorem infVec_fix (p : Bundle X ι) (x : X) :
    p.plusOne x *ᵥ (Sum.elim (0 : ι → ℂ) (fun _ : Unit => (1 : ℂ)))
      = Sum.elim (0 : ι → ℂ) (fun _ : Unit => (1 : ℂ)) := by
  refine (mem_plusOne_fibre_iff p x _).mpr ?_
  rw [infVec_comp_inl]
  exact Matrix.mulVec_zero _

omit [DecidableEq ι] in
theorem infPoint_mem_projSet (p : Bundle X ι) (x : X) :
    ((x, infPoint ι) : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ) ∈ projSet p.plusOne := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact conjTranspose_eq_of_isStarProjection
      (isStarProjection_rankOneProj (infVec_mem_unitVectors (ι := ι)))
  · exact (isStarProjection_rankOneProj (infVec_mem_unitVectors (ι := ι))).isIdempotentElem.eq
  · exact trace_rankOneProj (infVec_mem_unitVectors (ι := ι))
  · exact mul_rankOneProj_self (infVec_fix p x)

/-- **The zero section of `P(p ⊕ 1)`.** -/
noncomputable def zeroSectionProj (p : Bundle X ι) : C(X, Proj p.plusOne) where
  toFun x := ⟨(x, infPoint ι), infPoint_mem_projSet p x⟩
  continuous_toFun := (continuous_id.prodMk continuous_const).subtype_mk _

omit [DecidableEq ι] in
@[simp]
theorem zeroSectionProj_apply (p : Bundle X ι) (x : X) :
    (zeroSectionProj p x : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ) = (x, infPoint ι) := rfl

omit [DecidableEq ι] in
theorem projPi_comp_zeroSectionProj (p : Bundle X ι) :
    (projPi p.plusOne).comp (zeroSectionProj p) = ContinuousMap.id X := rfl

/-! ### The complement of the zero section -/

/-- The trace of the `ι`-block: it vanishes exactly on the zero section. -/
noncomputable def zTrace (z : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ) : ℂ :=
  (blockProj ι * z.2 * (blockProj ι)ᴴ).trace

theorem continuous_zTrace :
    Continuous (zTrace : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ → ℂ) :=
  ((continuous_const.matrix_mul continuous_snd).matrix_mul continuous_const).matrix_trace

omit [TopologicalSpace X] in
theorem zTrace_of_rankOneProj (x : X) (w : ι ⊕ Unit → ℂ) :
    zTrace ((x, rankOneProj w) : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ)
      = ((eucNormSq (w ∘ Sum.inl) : ℝ) : ℂ) := by
  show (blockProj ι * rankOneProj w * (blockProj ι)ᴴ).trace = _
  rw [conj_rankOneProj, blockProj_mulVec, trace_rankOneProj_eq]

/-- **The zero section is exactly the vanishing of the `ι`-block trace.** -/
theorem zTrace_eq_zero_iff {p : Bundle X ι} {z : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ}
    (hz : z ∈ projSet p.plusOne) : zTrace z = 0 ↔ z.2 = infPoint ι := by
  obtain ⟨w, hw, hzw, -⟩ := exists_unitVector_of_mem_projSet hz
  have htr : zTrace z = ((eucNormSq (w ∘ Sum.inl) : ℝ) : ℂ) := by
    show (blockProj ι * z.2 * (blockProj ι)ᴴ).trace = _
    rw [hzw, conj_rankOneProj, blockProj_mulVec, trace_rankOneProj_eq]
  constructor
  · intro h0
    have hz0 : eucNormSq (w ∘ Sum.inl) = 0 := by
      have hc : ((eucNormSq (w ∘ Sum.inl) : ℝ) : ℂ) = 0 := by rw [← htr]; exact h0
      exact_mod_cast hc
    have hl : (w ∘ Sum.inl) = (0 : ι → ℂ) := eucNormSq_eq_zero_iff.mp hz0
    have hlam : eucNormSq (w ∘ Sum.inr) = 1 := by
      have h1 : eucNormSq (w ∘ Sum.inl) + eucNormSq (w ∘ Sum.inr) = 1 := by
        rw [← eucNormSq_sum_type]
        exact mem_unitVectors_iff_eucNormSq.mp hw
      rw [hz0, zero_add] at h1
      exact h1
    have hnorm : ‖w (Sum.inr ())‖ ^ 2 = 1 := by
      have hc : eucNormSq (w ∘ Sum.inr) = ‖w (Sum.inr ())‖ ^ 2 := by
        rw [eucNormSq_def]
        simp
      rw [← hc]
      exact hlam
    have hsplit : w = (w (Sum.inr ())) • Sum.elim (0 : ι → ℂ) (fun _ : Unit => (1 : ℂ)) := by
      funext s
      cases s with
      | inl i =>
          have hi := congrFun hl i
          show w (Sum.inl i) = _
          simpa using hi
      | inr u =>
          cases u
          show w (Sum.inr ()) = w (Sum.inr ()) * 1
          rw [mul_one]
    rw [hzw, hsplit, rankOneProj_smul, hnorm, Complex.ofReal_one, one_smul]
    rfl
  · intro h
    show (blockProj ι * z.2 * (blockProj ι)ᴴ).trace = 0
    rw [h, infPoint, conj_rankOneProj, blockProj_mulVec, trace_rankOneProj_eq, infVec_comp_inl,
      eucNormSq_eq_zero_iff.mpr rfl, Complex.ofReal_zero]

/-- `P(p ⊕ 1)` minus the zero section. -/
def notZeroSet (p : Bundle X ι) : Set (X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ) :=
  {z | z ∈ projSet p.plusOne ∧ zTrace z ≠ 0}

/-- `P(p ⊕ 1) ∖ Z` as a topological space. -/
abbrev NotZero (p : Bundle X ι) : Type := ↥(notZeroSet p)

theorem notZeroSet_subset (p : Bundle X ι) : notZeroSet p ⊆ projSet p.plusOne :=
  fun _ hz => hz.1

/-- The complement of the zero section is open in `P(p ⊕ 1)`. -/
theorem isOpen_notZero_in_proj (p : Bundle X ι) :
    IsOpen {z : Proj p.plusOne | zTrace (z : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ) ≠ 0} := by
  have h : {z : Proj p.plusOne | zTrace (z : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ) ≠ 0}
      = (fun z : Proj p.plusOne => zTrace (z : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ)) ⁻¹'
        ({(0 : ℂ)}ᶜ) := rfl
  rw [h]
  exact IsOpen.preimage (continuous_zTrace.comp continuous_subtype_val) isOpen_compl_singleton

/-- The complement of the zero section, as a subspace of `P(p ⊕ 1)`. -/
def notZeroToProj (p : Bundle X ι) : C(NotZero p, Proj p.plusOne) :=
  ⟨Set.inclusion (notZeroSet_subset p), continuous_inclusion _⟩

/-- A point off the zero section is spanned by a unit vector with nonzero
`ι`-part. -/
theorem exists_spanning_of_notZero (p : Bundle X ι) (z : NotZero p) :
    ∃ w ∈ unitVectors (ι ⊕ Unit),
      (z : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ).2 = rankOneProj w ∧ w ∘ Sum.inl ≠ 0 := by
  obtain ⟨w, hw, hzw, -⟩ := exists_unitVector_of_mem_projSet z.2.1
  refine ⟨w, hw, hzw, ?_⟩
  intro h
  refine z.2.2 ?_
  show (blockProj ι * (z : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ).2 * (blockProj ι)ᴴ).trace = 0
  rw [hzw, conj_rankOneProj, blockProj_mulVec, trace_rankOneProj_eq, h,
    eucNormSq_eq_zero_iff.mpr rfl, Complex.ofReal_zero]

/-! ### The retraction onto `P(p)` -/

theorem projRetract_mem (p : Bundle X ι) (z : NotZero p) :
    (((z : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ).1,
        conjNormalize (blockProj ι) (z : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ).2)
      : X × Matrix ι ι ℂ) ∈ projSet p :=
  conjNormalize_mem_projFibreSet' (blockProj_fix p _) z.2.1 z.2.2

/-- **The retraction `P(p ⊕ 1) ∖ Z → P(p)`**, in coordinates `[v : λ] ↦ [v : 0]`. -/
noncomputable def projRetract (p : Bundle X ι) : C(NotZero p, Proj p) where
  toFun z := ⟨((z : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ).1,
      conjNormalize (blockProj ι) (z : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ).2),
    projRetract_mem p z⟩
  continuous_toFun :=
    ((continuous_fst.comp continuous_subtype_val).prodMk
      (continuous_conjNormalize continuous_const
        (continuous_snd.comp continuous_subtype_val) fun z => z.2.2)).subtype_mk _

@[simp]
theorem projRetract_apply (p : Bundle X ι) (z : NotZero p) :
    (projRetract p z : X × Matrix ι ι ℂ)
      = ((z : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ).1,
          conjNormalize (blockProj ι) (z : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ).2) := rfl

theorem projIncl_mem_notZeroSet (p : Bundle X ι) (z : Proj p) :
    (projIncl p z : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ) ∈ notZeroSet p := by
  refine ⟨(projIncl p z).2, ?_⟩
  show (blockProj ι * inclMat (z : X × Matrix ι ι ℂ).2 * (blockProj ι)ᴴ).trace ≠ 0
  rw [blockProj_conj_inclMat, z.2.2.2.1]
  exact one_ne_zero

/-- `P(p)` sits inside the complement of the zero section. -/
noncomputable def projInclNotZero (p : Bundle X ι) : C(Proj p, NotZero p) where
  toFun z := ⟨(projIncl p z : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ), projIncl_mem_notZeroSet p z⟩
  continuous_toFun := (continuous_subtype_val.comp (projIncl p).continuous).subtype_mk _

theorem projRetract_projInclNotZero (p : Bundle X ι) (z : Proj p) :
    projRetract p (projInclNotZero p z) = z := by
  apply Subtype.ext
  refine Prod.ext rfl ?_
  show conjNormalize (blockProj ι) (inclMat (z : X × Matrix ι ι ℂ).2)
      = (z : X × Matrix ι ι ℂ).2
  rw [conjNormalize_def, blockProj_conj_inclMat, z.2.2.2.1, inv_one, one_smul]

/-! ### The deformation `[v : λ] ↦ [v : tλ]` -/

/-- `diag(1, t)`: the matrix implementing `[v : λ] ↦ [v : tλ]`. -/
def lastScale (ι : Type) [Fintype ι] [DecidableEq ι] (t : ℂ) :
    Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ :=
  Matrix.fromBlocks 1 0 0 (t • 1)

theorem lastScale_one : lastScale ι (1 : ℂ) = 1 := by
  rw [lastScale, one_smul, Matrix.fromBlocks_one]

theorem lastScale_mulVec (t : ℂ) (w : ι ⊕ Unit → ℂ) :
    lastScale ι t *ᵥ w = Sum.elim (w ∘ Sum.inl) (t • (w ∘ Sum.inr)) := by
  rw [lastScale, Matrix.fromBlocks_mulVec]
  simp [Matrix.smul_mulVec]

/-- The `ι`-part of a vector is untouched, which is why the deformation never
leaves the complement of the zero section, even at `t = 0`. -/
theorem lastScale_mulVec_comp_inl (t : ℂ) (w : ι ⊕ Unit → ℂ) :
    (lastScale ι t *ᵥ w) ∘ Sum.inl = w ∘ Sum.inl := by
  rw [lastScale_mulVec]
  rfl

theorem lastScale_comm (p : Bundle X ι) (x : X) (t : ℂ) :
    lastScale ι t * p.plusOne x = p.plusOne x * lastScale ι t := by
  rw [lastScale, plusOne_apply, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp

theorem lastScale_fix (p : Bundle X ι) (x : X) (t : ℂ) (u : ι ⊕ Unit → ℂ)
    (hu : p.plusOne x *ᵥ u = u) :
    p.plusOne x *ᵥ (lastScale ι t *ᵥ u) = lastScale ι t *ᵥ u := by
  rw [Matrix.mulVec_mulVec, ← lastScale_comm, ← Matrix.mulVec_mulVec, hu]

theorem continuous_lastScale : Continuous (lastScale ι) := by
  refine continuous_matrix fun s s' => ?_
  cases s with
  | inl i =>
      cases s' with
      | inl j => exact continuous_const
      | inr u => exact continuous_const
  | inr u =>
      cases s' with
      | inl j => exact continuous_const
      | inr u' =>
          show Continuous fun t : ℂ => t * (1 : Matrix Unit Unit ℂ) u u'
          exact continuous_id.mul continuous_const

omit [TopologicalSpace X] in
theorem zTrace_lineOf_ne_zero (x : X) {v : ι ⊕ Unit → ℂ} (hv : v ≠ 0)
    (hvl : v ∘ Sum.inl ≠ 0) :
    zTrace ((x, lineOf v) : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ) ≠ 0 := by
  have hpos : 0 < Real.sqrt (eucNormSq v) := Real.sqrt_pos.mpr (eucNormSq_pos hv)
  have hc : (((Real.sqrt (eucNormSq v))⁻¹ : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (inv_pos.mpr hpos))
  have hnl : (normalizeVec v) ∘ Sum.inl
      = (((Real.sqrt (eucNormSq v))⁻¹ : ℝ) : ℂ) • (v ∘ Sum.inl) := rfl
  have hne : (normalizeVec v) ∘ Sum.inl ≠ 0 := by
    rw [hnl]
    exact smul_ne_zero_of_ne_zero hc hvl
  rw [lineOf_eq_rankOneProj_normalizeVec hv, zTrace_of_rankOneProj]
  simpa using eucNormSq_ne_zero hne

theorem lastScale_mulVec_ne_zero {w : ι ⊕ Unit → ℂ} (hwl : w ∘ Sum.inl ≠ 0) (t : ℂ) :
    lastScale ι t *ᵥ w ≠ 0 := by
  intro h
  refine hwl ?_
  rw [← lastScale_mulVec_comp_inl t w, h]
  rfl

theorem lastScale_trace_ne_zero (p : Bundle X ι) (t : ℂ) (z : NotZero p) :
    (lastScale ι t * (z : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ).2
      * (lastScale ι t)ᴴ).trace ≠ 0 := by
  obtain ⟨w, -, hzw, hwl⟩ := exists_spanning_of_notZero p z
  rw [hzw, conj_rankOneProj, trace_rankOneProj_eq]
  simpa using eucNormSq_ne_zero (lastScale_mulVec_ne_zero hwl t)

theorem retractHomotopy_mem (p : Bundle X ι) (t : I) (z : NotZero p) :
    (((z : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ).1,
        conjNormalize (lastScale ι (((t : ℝ) : ℂ)))
          (z : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ).2)
      : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ) ∈ notZeroSet p := by
  obtain ⟨w, -, hzw, hwl⟩ := exists_spanning_of_notZero p z
  have hne : lastScale ι (((t : ℝ) : ℂ)) *ᵥ w ≠ 0 := lastScale_mulVec_ne_zero hwl _
  refine ⟨conjNormalize_mem_projFibreSet' (lastScale_fix p _ _) z.2.1
      (lastScale_trace_ne_zero p _ z), ?_⟩
  have hval : conjNormalize (lastScale ι (((t : ℝ) : ℂ)))
      (z : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ).2
      = lineOf (lastScale ι (((t : ℝ) : ℂ)) *ᵥ w) := by
    rw [hzw, conjNormalize_rankOneProj]
  show zTrace (((z : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ).1, _)
      : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ) ≠ 0
  rw [hval]
  exact zTrace_lineOf_ne_zero _ hne (by rw [lastScale_mulVec_comp_inl]; exact hwl)

/-- The deformation of `P(p ⊕ 1) ∖ Z` onto `P(p)`. -/
noncomputable def retractHomotopy (p : Bundle X ι) :
    ContinuousMap.Homotopy ((projInclNotZero p).comp (projRetract p))
      (ContinuousMap.id (NotZero p)) where
  toFun tz := ⟨((tz.2 : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ).1,
      conjNormalize (lastScale ι (((tz.1 : ℝ) : ℂ)))
        (tz.2 : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ).2),
    retractHomotopy_mem p tz.1 tz.2⟩
  continuous_toFun :=
    ((continuous_fst.comp (continuous_subtype_val.comp continuous_snd)).prodMk
      (continuous_conjNormalize
        (continuous_lastScale.comp
          (Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)))
        (continuous_snd.comp (continuous_subtype_val.comp continuous_snd))
        fun tz => lastScale_trace_ne_zero p _ tz.2)).subtype_mk _
  map_zero_left z := by
    obtain ⟨w, -, hzw, hwl⟩ := exists_spanning_of_notZero p z
    apply Subtype.ext
    refine Prod.ext rfl ?_
    show conjNormalize (lastScale ι ((((0 : I) : ℝ) : ℂ)))
        (z : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ).2
      = inclMat (conjNormalize (blockProj ι) (z : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ).2)
    rw [hzw, conjNormalize_rankOneProj, conjNormalize_rankOneProj, blockProj_mulVec,
      lastScale_mulVec]
    have hz0 : ((((0 : I) : ℝ) : ℂ)) • (w ∘ Sum.inr) = (0 : Unit → ℂ) := by
      simp
    rw [hz0, lineOf_sum_elim_zero]
  map_one_left z := by
    apply Subtype.ext
    refine Prod.ext rfl ?_
    show conjNormalize (lastScale ι ((((1 : I) : ℝ) : ℂ)))
        (z : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ).2
      = (z : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ).2
    have h1 : ((((1 : I) : ℝ) : ℂ)) = (1 : ℂ) := by simp
    rw [h1, lastScale_one, conjNormalize_def, Matrix.one_mul, Matrix.conjTranspose_one,
      Matrix.mul_one, z.2.1.2.2.1, inv_one, one_smul]

/-- **`P(p ⊕ 1)` minus the zero section deformation retracts onto `P(p)`.**  This
is the input to the Gysin sequence: the Mayer-Vietoris of
`P(L ⊕ 1) = E(L) ∪ (P(L⊕1) ∖ Z)` has this space as one of its two opens. -/
noncomputable def notZeroHomotopyEquivProj (p : Bundle X ι) :
    ContinuousMap.HomotopyEquiv (NotZero p) (Proj p) where
  toFun := projRetract p
  invFun := projInclNotZero p
  left_inv := ⟨retractHomotopy p⟩
  right_inv := by
    have h : (projRetract p).comp (projInclNotZero p) = ContinuousMap.id (Proj p) :=
      ContinuousMap.ext fun z => projRetract_projInclNotZero p z
    rw [h]

end ZeroSection

end Bundle

end CharClass
end GroupApproximation
