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
  rw [eucNormSq, eucNormSq, eucNormSq, Fintype.sum_sum_type]
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

@[simp]
theorem inclMat_apply_inl_inl (q : Matrix ι ι ℂ) (i j : ι) :
    inclMat q (Sum.inl i) (Sum.inl j) = q i j := rfl

@[simp]
theorem inclMat_apply_inr_inr (q : Matrix ι ι ℂ) (u u' : Unit) :
    inclMat q (Sum.inr u) (Sum.inr u') = 0 := rfl

theorem inclMat_conjTranspose (q : Matrix ι ι ℂ) : (inclMat q)ᴴ = inclMat (qᴴ) := by
  rw [inclMat, inclMat, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero]

theorem inclMat_mul (q q' : Matrix ι ι ℂ) : inclMat q * inclMat q' = inclMat (q * q') := by
  rw [inclMat, inclMat, inclMat, Matrix.fromBlocks_multiply]
  simp

theorem trace_inclMat (q : Matrix ι ι ℂ) : (inclMat q).trace = q.trace := by
  rw [inclMat, trace_fromBlocks, Matrix.trace_zero, add_zero]

theorem plusOne_mul_inclMat (p : Bundle X ι) (x : X) (q : Matrix ι ι ℂ) :
    p.plusOne x * inclMat q = inclMat (p x * q) := by
  rw [plusOne_apply, inclMat, inclMat, Matrix.fromBlocks_multiply]
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

theorem continuous_betaEntry :
    Continuous (betaEntry : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ → ℂ) :=
  (continuous_snd.matrix_elem (Sum.inr ()) (Sum.inr ()))

/-- **The hyperplane at infinity is exactly the vanishing of one entry.** -/
theorem betaEntry_eq_zero_iff {p : Bundle X ι} {z : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ}
    (hz : z ∈ projSet p.plusOne) :
    betaEntry z = 0 ↔ ∃ z' : X × Matrix ι ι ℂ, z' ∈ projSet p ∧ z = (z'.1, inclMat z'.2) := by
  obtain ⟨w, hw, hzw, hfix⟩ := exists_unitVector_of_mem_projSet hz
  have hbeta : betaEntry z = ((‖w (Sum.inr ())‖ ^ 2 : ℝ) : ℂ) := by
    rw [betaEntry, hzw, rankOneProj_apply]
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

end Chart

end Bundle

end CharClass
end GroupApproximation
