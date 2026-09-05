import GroupApproximation.CharClass.BundleSpace

/-!
# Complex vector bundles in the projection model, V: the projective completion

The decomposition every characteristic-class argument is built on:

    P(p ⊕ 1) = E(p) ⊔ P(p),   E(p) open,   P(p) closed,

with `E(p) ∋ v ↦ [v : 1]` the affine chart and `P(p)` the hyperplane at
infinity `[v : 0]`.  Both halves are computed **entrywise**: a point of
`P(p ⊕ 1)` is a rank-one projection `Q` on `ℂ^ι ⊕ ℂ`, the coordinate at infinity
is the single entry `Q_{**}` (the `Sum.inr` diagonal entry), and the chart's
inverse is the ratio `v i = Q_{i*} / Q_{**}` -- no choice of a spanning vector
is involved, so the inverse is manifestly continuous.  The spanning vector is
used only in the *proofs*, where `STW59.eq_rankOneProj_of_trace_one` supplies
it.

## Manuscript status

Machinery.  Certifies no manuscript step on its own.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open scoped Matrix
open GroupApproximation.STW59

namespace Bundle

section Chart

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι]

/-! ### Vectors and matrices split along `ι ⊕ Unit` -/

theorem eucNormSq_sum_type {κ : Type} [Fintype κ] (w : ι ⊕ κ → ℂ) :
    eucNormSq w = eucNormSq (w ∘ Sum.inl) + eucNormSq (w ∘ Sum.inr) := by
  rw [eucNormSq_def, eucNormSq_def, eucNormSq_def, Fintype.sum_sum_type]
  rfl

theorem sum_elim_eta (w : ι ⊕ Unit → ℂ) :
    w = Sum.elim (fun i => w (Sum.inl i)) (fun _ => w (Sum.inr ())) := by
  funext s
  cases s with
  | inl i => rfl
  | inr u => cases u; rfl

theorem plusOne_mulVec (p : Bundle X ι) (x : X) (w : ι ⊕ Unit → ℂ) :
    p.plusOne x *ᵥ w = Sum.elim (p x *ᵥ (w ∘ Sum.inl)) (w ∘ Sum.inr) := by
  rw [plusOne_apply, Matrix.fromBlocks_mulVec]
  simp

/-- A vector lies in the fibre of `p ⊕ 1` exactly when its `ι`-part lies in the
fibre of `p`; the last coordinate is unconstrained. -/
theorem mem_plusOne_fibre_iff (p : Bundle X ι) (x : X) (w : ι ⊕ Unit → ℂ) :
    p.plusOne x *ᵥ w = w ↔ p x *ᵥ (w ∘ Sum.inl) = w ∘ Sum.inl := by
  rw [plusOne_mulVec]
  constructor
  · intro h
    funext i
    have hi := congrFun h (Sum.inl i)
    simpa using hi
  · intro h
    funext s
    cases s with
    | inl i =>
        have hi := congrFun h i
        simpa using hi
    | inr u => cases u; rfl

/-- The `ι`-block embedding of a matrix, `q ↦ diag(q, 0)`. -/
def inclMat (q : Matrix ι ι ℂ) : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ := Matrix.fromBlocks q 0 0 0

theorem inclMat_def (q : Matrix ι ι ℂ) : inclMat q = Matrix.fromBlocks q 0 0 0 := rfl

@[simp]
theorem inclMat_apply_inl_inl (q : Matrix ι ι ℂ) (i j : ι) :
    inclMat q (Sum.inl i) (Sum.inl j) = q i j := rfl

@[simp]
theorem inclMat_apply_inr_inr (q : Matrix ι ι ℂ) (u u' : Unit) :
    inclMat q (Sum.inr u) (Sum.inr u') = 0 := rfl

theorem inclMat_conjTranspose (q : Matrix ι ι ℂ) : (inclMat q)ᴴ = inclMat (qᴴ) := by
  simp only [inclMat_def, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero]

theorem inclMat_mul (q q' : Matrix ι ι ℂ) : inclMat q * inclMat q' = inclMat (q * q') := by
  rw [inclMat_def, inclMat_def, inclMat_def, Matrix.fromBlocks_multiply]
  simp

theorem trace_inclMat (q : Matrix ι ι ℂ) : (inclMat q).trace = q.trace := by
  rw [inclMat_def, trace_fromBlocks, Matrix.trace_zero, add_zero]

theorem plusOne_mul_inclMat (p : Bundle X ι) (x : X) (q : Matrix ι ι ℂ) :
    p.plusOne x * inclMat q = inclMat (p x * q) := by
  rw [plusOne_apply, inclMat_def, inclMat_def, Matrix.fromBlocks_multiply]
  simp

theorem continuous_inclMat :
    Continuous (inclMat : Matrix ι ι ℂ → Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ) := by
  refine continuous_matrix fun i j => ?_
  cases i with
  | inl i =>
      cases j with
      | inl j => exact continuous_id.matrix_elem i j
      | inr j => exact continuous_const
  | inr i =>
      cases j with
      | inl j => exact continuous_const
      | inr j => exact continuous_const

theorem inclMat_injective : Function.Injective (inclMat : Matrix ι ι ℂ → _) := by
  intro q q' h
  ext i j
  have := congrFun (congrFun h (Sum.inl i)) (Sum.inl j)
  simpa using this

/-! ### `P(p)` sits inside `P(p ⊕ 1)` -/

/-- The hyperplane at infinity: `P(p) ⊆ P(p ⊕ 1)`. -/
def projIncl (p : Bundle X ι) : C(Proj p, Proj p.plusOne) where
  toFun z := ⟨((z : X × Matrix ι ι ℂ).1, inclMat (z : X × Matrix ι ι ℂ).2), by
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [inclMat_conjTranspose, z.2.1]
      · rw [inclMat_mul, z.2.2.1]
      · rw [trace_inclMat, z.2.2.2.1]
      · rw [plusOne_mul_inclMat, z.2.2.2.2]⟩
  continuous_toFun :=
    ((continuous_fst.comp continuous_subtype_val).prodMk
      (continuous_inclMat.comp (continuous_snd.comp continuous_subtype_val))).subtype_mk _

@[simp]
theorem projIncl_apply (p : Bundle X ι) (z : Proj p) :
    (projIncl p z : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ)
      = ((z : X × Matrix ι ι ℂ).1, inclMat (z : X × Matrix ι ι ℂ).2) := rfl

theorem projIncl_injective (p : Bundle X ι) : Function.Injective (projIncl p) := by
  intro z z' h
  have h' := congrArg (fun w : Proj p.plusOne => (w : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ)) h
  rw [projIncl_apply, projIncl_apply] at h'
  apply Subtype.ext
  refine Prod.ext (congrArg Prod.fst h') (inclMat_injective (congrArg Prod.snd h'))

/-! ### The spanning vector of a point of the projective bundle -/

theorem rankOneProj_mulVec_self {u : ι → ℂ} (hu : u ∈ unitVectors ι) :
    rankOneProj u *ᵥ u = u := by
  rw [← lineOf_of_mem_unitVectors hu]
  exact lineOf_mulVec_self (ne_zero_of_eucNormSq_eq_one hu)

/-- Every point of `P(p)` is the line spanned by a unit vector of the fibre. -/
theorem exists_unitVector_of_mem_projSet {p : Bundle X ι} {z : X × Matrix ι ι ℂ}
    (hz : z ∈ projSet p) :
    ∃ u ∈ unitVectors ι, z.2 = rankOneProj u ∧ p z.1 *ᵥ u = u := by
  obtain ⟨u, hu, hzu⟩ :=
    eq_rankOneProj_of_trace_one (isStarProjection_of_mem_projSet hz) (trace_of_mem_projSet hz)
  refine ⟨u, hu, hzu, ?_⟩
  have h : p z.1 * rankOneProj u = rankOneProj u := by
    rw [← hzu]; exact absorb_of_mem_projSet hz
  have h2 : p z.1 *ᵥ (rankOneProj u *ᵥ u) = rankOneProj u *ᵥ u := by
    rw [Matrix.mulVec_mulVec, h]
  rwa [rankOneProj_mulVec_self hu] at h2

/-! ### The coordinate at infinity -/

/-- The entry that vanishes exactly on the hyperplane at infinity. -/
def betaEntry (z : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ) : ℂ :=
  z.2 (Sum.inr ()) (Sum.inr ())

theorem betaEntry_def (z : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ) :
    betaEntry z = z.2 (Sum.inr ()) (Sum.inr ()) := rfl

theorem continuous_betaEntry :
    Continuous (betaEntry : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ → ℂ) :=
  (continuous_snd.matrix_elem (Sum.inr ()) (Sum.inr ()))

/-- **The hyperplane at infinity is exactly the vanishing of one entry.** -/
theorem betaEntry_eq_zero_iff {p : Bundle X ι} {z : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ}
    (hz : z ∈ projSet p.plusOne) :
    betaEntry z = 0 ↔ ∃ z' : X × Matrix ι ι ℂ, z' ∈ projSet p ∧ z = (z'.1, inclMat z'.2) := by
  obtain ⟨w, hw, hzw, hfix⟩ := exists_unitVector_of_mem_projSet hz
  have hbeta : betaEntry z = ((‖w (Sum.inr ())‖ ^ 2 : ℝ) : ℂ) := by
    rw [betaEntry_def, hzw, rankOneProj_apply]
    exact mul_star_self_eq_normSq _
  constructor
  · intro h0
    have hlam : w (Sum.inr ()) = 0 := by
      have : ((‖w (Sum.inr ())‖ ^ 2 : ℝ) : ℂ) = 0 := by rw [← hbeta]; exact h0
      have h2 : ‖w (Sum.inr ())‖ ^ 2 = 0 := by exact_mod_cast this
      have h3 : ‖w (Sum.inr ())‖ = 0 := by nlinarith [norm_nonneg (w (Sum.inr ()))]
      simpa using h3
    have hzero : (w ∘ Sum.inr) = (0 : Unit → ℂ) := by
      funext u
      cases u
      exact hlam
    have hwl : (w ∘ Sum.inl) ∈ unitVectors ι := by
      rw [mem_unitVectors_iff_eucNormSq]
      have h1 : eucNormSq (w ∘ Sum.inl) + eucNormSq (w ∘ Sum.inr) = 1 := by
        rw [← eucNormSq_sum_type]
        exact mem_unitVectors_iff_eucNormSq.mp hw
      have h2 : eucNormSq (w ∘ Sum.inr) = 0 := by
        rw [hzero]
        simp [eucNormSq]
      linarith
    have hmat : z.2 = inclMat (rankOneProj (w ∘ Sum.inl)) := by
      rw [hzw]
      ext s t
      cases s with
      | inl i =>
          cases t with
          | inl j => rfl
          | inr u => cases u; simp [rankOneProj_apply, hlam, inclMat]
      | inr u =>
          cases u
          cases t with
          | inl j => simp [rankOneProj_apply, hlam, inclMat]
          | inr u' => cases u'; simp [rankOneProj_apply, hlam, inclMat]
    refine ⟨(z.1, rankOneProj (w ∘ Sum.inl)), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · exact conjTranspose_eq_of_isStarProjection (isStarProjection_rankOneProj hwl)
    · exact (isStarProjection_rankOneProj hwl).isIdempotentElem.eq
    · exact trace_rankOneProj hwl
    · exact mul_rankOneProj_self ((mem_plusOne_fibre_iff p z.1 w).mp hfix)
    · rw [← hmat]
  · rintro ⟨z', -, rfl⟩
    rfl

theorem range_projIncl (p : Bundle X ι) :
    Set.range (projIncl p)
      = {z : Proj p.plusOne | betaEntry (z : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ) = 0} := by
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    rfl
  · intro hz
    obtain ⟨z', hz', heq⟩ := (betaEntry_eq_zero_iff z.2).mp hz
    exact ⟨⟨z', hz'⟩, Subtype.ext heq.symm⟩

/-- **The hyperplane at infinity is closed.** -/
theorem isClosed_range_projIncl (p : Bundle X ι) : IsClosed (Set.range (projIncl p)) := by
  rw [range_projIncl]
  exact isClosed_eq (continuous_betaEntry.comp continuous_subtype_val) continuous_const

/-- The hyperplane at infinity is a closed embedding when the base is compact.
(The campaign's bases are all compact; without compactness the same statement
holds but needs the explicit inverse `Matrix.toBlocks₁₁`.) -/
theorem isClosedEmbedding_projIncl [CompactSpace X] [T2Space X] (p : Bundle X ι) :
    Topology.IsClosedEmbedding (projIncl p) :=
  (projIncl p).continuous.isClosedEmbedding (projIncl_injective p)

/-! ### The affine chart `E(p) ≅ P(p ⊕ 1) ∖ P(p)` -/

/-- The complement of the hyperplane at infinity in `P(p ⊕ 1)`. -/
def chartSet (p : Bundle X ι) : Set (X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ) :=
  {z | z ∈ projSet p.plusOne ∧ betaEntry z ≠ 0}

/-- `P(p ⊕ 1) ∖ P(p)` as a topological space. -/
abbrev Chart (p : Bundle X ι) : Type := ↥(chartSet p)

theorem chartSet_subset (p : Bundle X ι) : chartSet p ⊆ projSet p.plusOne := fun _ hz => hz.1

/-- The chart is an open subspace of `P(p ⊕ 1)`. -/
theorem isOpen_chart_in_proj (p : Bundle X ι) :
    IsOpen {z : Proj p.plusOne | betaEntry (z : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ) ≠ 0} := by
  have h : {z : Proj p.plusOne | betaEntry (z : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ) ≠ 0}
      = (fun z : Proj p.plusOne => betaEntry (z : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ)) ⁻¹'
        ({(0 : ℂ)}ᶜ) := rfl
  rw [h]
  exact IsOpen.preimage (continuous_betaEntry.comp continuous_subtype_val) isOpen_compl_singleton

/-- The chart, as a subspace of `P(p ⊕ 1)`. -/
def chartToProj (p : Bundle X ι) : C(Chart p, Proj p.plusOne) :=
  ⟨Set.inclusion (chartSet_subset p), continuous_inclusion _⟩

/-- The vector `v` of a fibre, extended by the last coordinate `1`. -/
def chartVec (v : X × (ι → ℂ)) : ι ⊕ Unit → ℂ := Sum.elim v.2 (fun _ => 1)

@[simp]
theorem chartVec_inl (v : X × (ι → ℂ)) (i : ι) : chartVec v (Sum.inl i) = v.2 i := rfl

@[simp]
theorem chartVec_inr (v : X × (ι → ℂ)) (u : Unit) : chartVec v (Sum.inr u) = 1 := rfl

theorem chartVec_ne_zero (v : X × (ι → ℂ)) : chartVec v ≠ 0 := by
  intro h
  have := congrFun h (Sum.inr ())
  simp at this

theorem chartVec_comp_inl (v : X × (ι → ℂ)) : chartVec v ∘ Sum.inl = v.2 := rfl

theorem continuous_chartVec {Z : Type} [TopologicalSpace Z] {f : Z → X × (ι → ℂ)}
    (hf : Continuous f) : Continuous fun z => chartVec (f z) := by
  refine continuous_pi fun s => ?_
  cases s with
  | inl i => exact (continuous_apply i).comp (continuous_snd.comp hf)
  | inr u => exact continuous_const

theorem eucNormSq_chartVec_ne_zero (v : X × (ι → ℂ)) :
    ((eucNormSq (chartVec v) : ℝ) : ℂ) ≠ 0 := by
  simpa using eucNormSq_ne_zero (chartVec_ne_zero v)

/-- The affine chart `E(p) → P(p ⊕ 1) ∖ P(p)`, `v ↦ [v : 1]`. -/
def chartOf (p : Bundle X ι) : C(Total p, Chart p) where
  toFun v :=
    ⟨((v : X × (ι → ℂ)).1, lineOf (chartVec (v : X × (ι → ℂ)))),
      mem_projSet_of_lineOf (chartVec_ne_zero _)
        ((mem_plusOne_fibre_iff p _ _).mpr (mem_totalSet_iff.mp v.2)),
      by
        have hN := eucNormSq_chartVec_ne_zero (v : X × (ι → ℂ))
        show lineOf (chartVec (v : X × (ι → ℂ))) (Sum.inr ()) (Sum.inr ()) ≠ 0
        rw [lineOf_apply]
        simpa using inv_ne_zero hN⟩
  continuous_toFun :=
    ((continuous_fst.comp continuous_subtype_val).prodMk
      (continuous_lineOf (continuous_chartVec continuous_subtype_val)
        fun v => chartVec_ne_zero _)).subtype_mk _

@[simp]
theorem chartOf_apply (p : Bundle X ι) (v : Total p) :
    (chartOf p v : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ)
      = ((v : X × (ι → ℂ)).1, lineOf (chartVec (v : X × (ι → ℂ)))) := rfl

/-- The inverse of the chart, read off two entries: `v i = Q_{i*} / Q_{**}`. -/
def vecOf (z : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ) : ι → ℂ :=
  fun i => z.2 (Sum.inl i) (Sum.inr ()) / betaEntry z

theorem continuous_vecOf {Z : Type} [TopologicalSpace Z]
    {f : Z → X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ} (hf : Continuous f)
    (hne : ∀ z, betaEntry (f z) ≠ 0) : Continuous fun z => vecOf (f z) := by
  refine continuous_pi fun i => ?_
  exact ((continuous_snd.comp hf).matrix_elem (Sum.inl i) (Sum.inr ())).div
    (continuous_betaEntry.comp hf) hne

/-- The chart's inverse, computed on a spanning vector. -/
theorem vecOf_eq_smul {z : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ} {w : ι ⊕ Unit → ℂ}
    (hzw : z.2 = rankOneProj w) (hbeta : betaEntry z ≠ 0) :
    vecOf z = (w (Sum.inr ()))⁻¹ • (w ∘ Sum.inl) := by
  have hbeta' : betaEntry z = w (Sum.inr ()) * star (w (Sum.inr ())) := by
    rw [betaEntry_def, hzw, rankOneProj_apply]
  have hlam : w (Sum.inr ()) ≠ 0 := by
    intro h
    apply hbeta
    rw [hbeta', h, zero_mul]
  have hstar : star (w (Sum.inr ())) ≠ 0 := star_ne_zero.mpr hlam
  funext i
  show z.2 (Sum.inl i) (Sum.inr ()) / betaEntry z = (w (Sum.inr ()))⁻¹ * w (Sum.inl i)
  rw [hzw, rankOneProj_apply, hbeta', hzw, rankOneProj_apply]
  field_simp
  ring

theorem vecOf_mem_totalSet {p : Bundle X ι} {z : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ}
    (hz : z ∈ chartSet p) : ((z.1, vecOf z) : X × (ι → ℂ)) ∈ totalSet p := by
  obtain ⟨w, hw, hzw, hfix⟩ := exists_unitVector_of_mem_projSet hz.1
  have hv := vecOf_eq_smul hzw hz.2
  show p z.1 *ᵥ vecOf z = vecOf z
  rw [hv, Matrix.mulVec_smul, (mem_plusOne_fibre_iff p z.1 w).mp hfix]

/-- The inverse chart `P(p ⊕ 1) ∖ P(p) → E(p)`. -/
def totalOf (p : Bundle X ι) : C(Chart p, Total p) where
  toFun z := ⟨((z : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ).1,
      vecOf (z : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ)), vecOf_mem_totalSet z.2⟩
  continuous_toFun :=
    ((continuous_fst.comp continuous_subtype_val).prodMk
      (continuous_vecOf continuous_subtype_val fun z => z.2.2)).subtype_mk _

theorem totalOf_chartOf (p : Bundle X ι) (v : Total p) : totalOf p (chartOf p v) = v := by
  apply Subtype.ext
  refine Prod.ext rfl ?_
  funext i
  have hN := eucNormSq_chartVec_ne_zero (v : X × (ι → ℂ))
  have hNi : ((eucNormSq (chartVec (v : X × (ι → ℂ))) : ℝ) : ℂ)⁻¹ ≠ 0 := inv_ne_zero hN
  show lineOf (chartVec (v : X × (ι → ℂ))) (Sum.inl i) (Sum.inr ()) /
      lineOf (chartVec (v : X × (ι → ℂ))) (Sum.inr ()) (Sum.inr ()) = (v : X × (ι → ℂ)).2 i
  rw [lineOf_apply, lineOf_apply]
  simp only [chartVec_inl, chartVec_inr, star_one, mul_one]
  field_simp

theorem chartOf_totalOf (p : Bundle X ι) (z : Chart p) : chartOf p (totalOf p z) = z := by
  obtain ⟨w, hw, hzw, hfix⟩ := exists_unitVector_of_mem_projSet z.2.1
  have hbeta' : betaEntry (z : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ)
      = w (Sum.inr ()) * star (w (Sum.inr ())) := by
    rw [betaEntry_def, hzw, rankOneProj_apply]
  have hlam : w (Sum.inr ()) ≠ 0 := by
    intro h
    apply z.2.2
    rw [hbeta', h, zero_mul]
  have hv := vecOf_eq_smul hzw z.2.2
  have hcv : chartVec ((z : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ).1,
      vecOf (z : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ)) = (w (Sum.inr ()))⁻¹ • w := by
    funext s
    cases s with
    | inl i =>
        show vecOf (z : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ) i
            = (w (Sum.inr ()))⁻¹ * w (Sum.inl i)
        rw [hv]
        rfl
    | inr u =>
        cases u
        show (1 : ℂ) = (w (Sum.inr ()))⁻¹ * w (Sum.inr ())
        rw [inv_mul_cancel₀ hlam]
  apply Subtype.ext
  refine Prod.ext rfl ?_
  show lineOf (chartVec ((z : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ).1,
      vecOf (z : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ)))
      = (z : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ).2
  rw [hcv, lineOf_smul (inv_ne_zero hlam), lineOf_of_mem_unitVectors hw, hzw]

/-- **The total space is the complement of the hyperplane at infinity**, and the
identification is a homeomorphism onto an open subspace of `P(p ⊕ 1)`. -/
def totalHomeoChart (p : Bundle X ι) : Total p ≃ₜ Chart p where
  toFun := chartOf p
  invFun := totalOf p
  left_inv := totalOf_chartOf p
  right_inv := chartOf_totalOf p
  continuous_toFun := (chartOf p).continuous
  continuous_invFun := (totalOf p).continuous

end Chart

end Bundle

end CharClass
end GroupApproximation
