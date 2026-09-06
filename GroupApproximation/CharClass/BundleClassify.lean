import GroupApproximation.CharClass.BundleZeroSection

/-!
# Complex vector bundles in the projection model, IX: classifying maps

In this model a line bundle over `X` **is** a map `X → ℂP^{K-1}`: a rank-one
projection-valued continuous function is literally a continuous function into
`STW59.CP d`, and `classifyOne` is that observation with the subtype bundling
made explicit.  Nothing is constructed and nothing is chosen.

The content of the file is the **rotation homotopy** that makes
`e(L) := f_L^* h` well defined on isomorphism classes.  Two isomorphic line
bundles `L ⊆ X × ℂ^ι` and `L' ⊆ X × ℂ^κ`, embedded into `ℂ^ι ⊕ ℂ^κ` in the two
obvious ways, have homotopic classifying maps: rotate

    v ↦ ((1-t)·v, t·φ v)

where `φ` is the implementing family of partial isometries.  In the projection
model that rotation is conjugation by the single *square* matrix

    rotSq t x = [ (1-t)·1   0 ]
                [ t·φ x     0 ]

followed by the normalization `conjNormalize`, which is defined because the
trace of the conjugate is `(1-t)² + t² > 0` for every real `t`.  Because
`rotSq` is square and block-structured, the whole computation is
`Matrix.fromBlocks` algebra: no entrywise sums appear anywhere.

Note that `rotSq t x` is **singular** at both ends, so the invertibility-based
`BundleLocal.conjNormalize_mem_projFibreSet` is unusable and
`BundleZeroSection.conjNormalize_mem_projFibreSet'` is what carries the file.

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

/-! ### The classifying map of a line bundle -/

section Classify

variable {X : Type} [TopologicalSpace X]

/-- **The classifying map of a line bundle**, `f_p : X → ℂP^d`.  A rank-one
projection-valued map *is* a map into the model of complex projective space. -/
def classifyOne {d : ℕ} (p : Bundle X (Fin (d + 1))) (hp : ∀ x, (p x).trace = 1) :
    C(X, CP d) where
  toFun x := ⟨p x, p.conjTranspose_eq x, p.mul_self x, hp x⟩
  continuous_toFun := p.continuous.subtype_mk _

@[simp]
theorem classifyOne_apply {d : ℕ} (p : Bundle X (Fin (d + 1))) (hp : ∀ x, (p x).trace = 1)
    (x : X) : (classifyOne p hp x : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) = p x := rfl

/-- The classifying map of the tautological line of `ℂP^d` is the identity. -/
theorem classifyOne_cpTaut (d : ℕ) :
    classifyOne (cpTaut d) (trace_cpTaut d) = ContinuousMap.id (CP d) :=
  ContinuousMap.ext fun _ => rfl

/-- The classifying map of a pullback is the composite. -/
theorem classifyOne_comap {Y : Type} [TopologicalSpace Y] {d : ℕ}
    (p : Bundle X (Fin (d + 1))) (hp : ∀ x, (p x).trace = 1) (f : C(Y, X)) :
    classifyOne (comap f p) (fun y => hp (f y)) = (classifyOne p hp).comp f :=
  ContinuousMap.ext fun _ => rfl

end Classify

/-! ### The two block embeddings -/

section Blocks

variable {X : Type} [TopologicalSpace X] {ι κ : Type} [Fintype ι] [Fintype κ]

/-- The `ι`-block embedding of a matrix into `Matrix (ι ⊕ κ)`. -/
def blockL (ι κ : Type) [Fintype ι] [Fintype κ] (q : Matrix ι ι ℂ) :
    Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ := Matrix.fromBlocks q 0 0 0

/-- The `κ`-block embedding of a matrix into `Matrix (ι ⊕ κ)`. -/
def blockR (ι κ : Type) [Fintype ι] [Fintype κ] (q : Matrix κ κ ℂ) :
    Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ := Matrix.fromBlocks 0 0 0 q

theorem blockL_def (q : Matrix ι ι ℂ) :
    blockL ι κ q = Matrix.fromBlocks q 0 0 0 := rfl

theorem blockR_def (q : Matrix κ κ ℂ) :
    blockR ι κ q = Matrix.fromBlocks 0 0 0 q := rfl

theorem continuous_blockL :
    Continuous (blockL ι κ : Matrix ι ι ℂ → Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ) := by
  refine continuous_matrix fun s s' => ?_
  cases s with
  | inl i =>
      cases s' with
      | inl j => exact continuous_id.matrix_elem i j
      | inr k => exact continuous_const
  | inr k =>
      cases s' with
      | inl j => exact continuous_const
      | inr k' => exact continuous_const

theorem continuous_blockR :
    Continuous (blockR ι κ : Matrix κ κ ℂ → Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ) := by
  refine continuous_matrix fun s s' => ?_
  cases s with
  | inl i =>
      cases s' with
      | inl j => exact continuous_const
      | inr k => exact continuous_const
  | inr k =>
      cases s' with
      | inl j => exact continuous_const
      | inr k' => exact continuous_id.matrix_elem k k'

end Blocks

/-! ### The rotation -/

section Rotation

variable {X : Type} [TopologicalSpace X] {ι κ : Type} [Fintype ι] [Fintype κ]
  [DecidableEq ι] [DecidableEq κ]
variable {L : Bundle X ι} {L' : Bundle X κ}

theorem star_ofReal' (r : ℝ) : star ((r : ℝ) : ℂ) = ((r : ℝ) : ℂ) := Complex.conj_ofReal r

omit [DecidableEq ι] [DecidableEq κ] in
theorem trace_of_iso (e : BundleIso L L') (x : X) : (L' x).trace = (L x).trace := by
  rw [← e.mul_conjTranspose x, Matrix.trace_mul_comm, e.conjTranspose_mul]

omit [DecidableEq ι] [DecidableEq κ] in
theorem mul_conjTranspose_hom (e : BundleIso L L') (x : X) :
    L x * (e.hom x)ᴴ = (e.hom x)ᴴ := by
  have h := congrArg Matrix.conjTranspose (e.hom_mul_right x)
  rwa [Matrix.conjTranspose_mul, L.conjTranspose_eq] at h

/-- A block embedding of a rank-one projection is a point of the projective
space of `ℂ^ι ⊕ ℂ^κ`, i.e. of `P(1)`. -/
theorem blockL_mem_projSet (hL : ∀ x, (L x).trace = 1) (x : X) :
    ((x, blockL ι κ (L x)) : X × Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ)
      ∈ projSet (triv X (ι ⊕ κ)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [blockL_def, Matrix.fromBlocks_conjTranspose]
    simp [L.conjTranspose_eq]
  · rw [blockL_def, Matrix.fromBlocks_multiply]
    simp [L.mul_self]
  · rw [blockL_def, trace_fromBlocks, Matrix.trace_zero, add_zero]
    exact hL x
  · rw [triv_apply, Matrix.one_mul]

theorem blockR_mem_projSet (hL' : ∀ x, (L' x).trace = 1) (x : X) :
    ((x, blockR ι κ (L' x)) : X × Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ)
      ∈ projSet (triv X (ι ⊕ κ)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [blockR_def, Matrix.fromBlocks_conjTranspose]
    simp [L'.conjTranspose_eq]
  · rw [blockR_def, Matrix.fromBlocks_multiply]
    simp [L'.mul_self]
  · rw [blockR_def, trace_fromBlocks, Matrix.trace_zero, zero_add]
    exact hL' x
  · rw [triv_apply, Matrix.one_mul]

/-- **The rotating family** `[ (1-t)·1 , 0 ; t·φ , 0 ]`.  It is singular at both
ends, which is why the normalized conjugation of `BundleZeroSection` is needed
rather than the invertible one of `BundleLocal`. -/
noncomputable def rotSq (e : BundleIso L L') (t : ℝ) (x : X) :
    Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ :=
  Matrix.fromBlocks (((1 - t : ℝ) : ℂ) • 1) 0 (((t : ℝ) : ℂ) • e.hom x) 0

theorem rotSq_mul_blockL (e : BundleIso L L') (t : ℝ) (x : X) :
    rotSq e t x * blockL ι κ (L x)
      = Matrix.fromBlocks (((1 - t : ℝ) : ℂ) • L x) 0 (((t : ℝ) : ℂ) • e.hom x) 0 := by
  rw [rotSq, blockL_def, Matrix.fromBlocks_multiply]
  simp [Matrix.smul_mul, e.hom_mul_right]

omit [DecidableEq κ] in
theorem rotSq_conjTranspose (e : BundleIso L L') (t : ℝ) (x : X) :
    (rotSq e t x)ᴴ
      = Matrix.fromBlocks (((1 - t : ℝ) : ℂ) • 1) (((t : ℝ) : ℂ) • (e.hom x)ᴴ) 0 0 := by
  rw [rotSq, Matrix.fromBlocks_conjTranspose]
  simp [Matrix.conjTranspose_smul, star_ofReal']

theorem rotSq_conj (e : BundleIso L L') (t : ℝ) (x : X) :
    rotSq e t x * blockL ι κ (L x) * (rotSq e t x)ᴴ
      = Matrix.fromBlocks ((((1 - t) * (1 - t) : ℝ) : ℂ) • L x)
          (((t * (1 - t) : ℝ) : ℂ) • (e.hom x)ᴴ)
          ((((1 - t) * t : ℝ) : ℂ) • e.hom x) (((t * t : ℝ) : ℂ) • L' x) := by
  rw [rotSq_mul_blockL, rotSq_conjTranspose, Matrix.fromBlocks_multiply]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_zero,
    Matrix.mul_one, add_zero, smul_smul, ← Complex.ofReal_mul,
    mul_conjTranspose_hom, e.mul_conjTranspose]

theorem trace_rotSq_conj (e : BundleIso L L') (hL : ∀ x, (L x).trace = 1) (t : ℝ) (x : X) :
    (rotSq e t x * blockL ι κ (L x) * (rotSq e t x)ᴴ).trace
      = ((((1 - t) * (1 - t) + t * t : ℝ)) : ℂ) := by
  rw [rotSq_conj, trace_fromBlocks, Matrix.trace_smul, Matrix.trace_smul,
    trace_of_iso e x, hL x]
  simp [Complex.ofReal_add, Complex.ofReal_mul]

theorem rot_coeff_pos (t : ℝ) : 0 < (1 - t) * (1 - t) + t * t := by
  nlinarith [sq_nonneg (2 * t - 1)]

theorem trace_rotSq_conj_ne_zero (e : BundleIso L L') (hL : ∀ x, (L x).trace = 1)
    (t : ℝ) (x : X) :
    (rotSq e t x * blockL ι κ (L x) * (rotSq e t x)ᴴ).trace ≠ 0 := by
  rw [trace_rotSq_conj e hL t x]
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt (rot_coeff_pos t))

theorem rotSq_conj_mem (e : BundleIso L L') (hL : ∀ x, (L x).trace = 1) (t : ℝ) (x : X) :
    ((x, conjNormalize (rotSq e t x) (blockL ι κ (L x)))
      : X × Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ) ∈ projSet (triv X (ι ⊕ κ)) := by
  refine conjNormalize_mem_projFibreSet' (q := (1 : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ)) ?_
    (blockL_mem_projSet hL x) (trace_rotSq_conj_ne_zero e hL t x)
  intro u _
  exact Matrix.one_mulVec _

/-! ### The two classifying sections and the homotopy between them -/

/-- The classifying map of `L`, embedded into the `ι`-block of `ℂ^ι ⊕ ℂ^κ`. -/
def classL (κ : Type) [Fintype κ] [DecidableEq κ] (L : Bundle X ι)
    (hL : ∀ x, (L x).trace = 1) : C(X, Proj (triv X (ι ⊕ κ))) where
  toFun x := ⟨(x, blockL ι κ (L x)), blockL_mem_projSet hL x⟩
  continuous_toFun :=
    (continuous_id.prodMk (continuous_blockL.comp L.continuous)).subtype_mk _

/-- The classifying map of `L'`, embedded into the `κ`-block. -/
def classR (ι : Type) [Fintype ι] [DecidableEq ι] (L' : Bundle X κ)
    (hL' : ∀ x, (L' x).trace = 1) : C(X, Proj (triv X (ι ⊕ κ))) where
  toFun x := ⟨(x, blockR ι κ (L' x)), blockR_mem_projSet hL' x⟩
  continuous_toFun :=
    (continuous_id.prodMk (continuous_blockR.comp L'.continuous)).subtype_mk _

/-- The rotation homotopy. -/
noncomputable def rotHomotopy (e : BundleIso L L') (hL : ∀ x, (L x).trace = 1) :
    ContinuousMap.Homotopy (classL κ L hL)
      (classR ι L' (fun x => by rw [trace_of_iso e x]; exact hL x)) where
  toFun tx := ⟨(tx.2, conjNormalize (rotSq e ((tx.1 : ℝ)) tx.2) (blockL ι κ (L tx.2))),
    rotSq_conj_mem e hL _ _⟩
  continuous_toFun := by
    have hrot : Continuous fun tx : I × X => rotSq e ((tx.1 : ℝ)) tx.2 := by
      refine continuous_matrix fun s s' => ?_
      cases s with
      | inl i =>
          cases s' with
          | inl j =>
              show Continuous fun tx : I × X =>
                (((1 - (tx.1 : ℝ) : ℝ) : ℂ) • (1 : Matrix ι ι ℂ)) i j
              exact (((Complex.continuous_ofReal.comp
                (continuous_const.sub (continuous_subtype_val.comp continuous_fst))).smul
                  continuous_const)).matrix_elem i j
          | inr k => exact continuous_const
      | inr k =>
          cases s' with
          | inl j =>
              show Continuous fun tx : I × X =>
                ((((tx.1 : ℝ) : ℂ)) • e.hom tx.2) k j
              exact (((Complex.continuous_ofReal.comp
                (continuous_subtype_val.comp continuous_fst)).smul
                  (e.continuous_hom.comp continuous_snd))).matrix_elem k j
          | inr k' => exact continuous_const
    exact (continuous_snd.prodMk
      (continuous_conjNormalize hrot (continuous_blockL.comp (L.continuous.comp continuous_snd))
        fun tx => trace_rotSq_conj_ne_zero e hL _ _)).subtype_mk _
  map_zero_left x := by
    apply Subtype.ext
    refine Prod.ext rfl ?_
    show conjNormalize (rotSq e ((((0 : I) : ℝ))) x) (blockL ι κ (L x)) = blockL ι κ (L x)
    rw [conjNormalize_def, trace_rotSq_conj e hL, rotSq_conj, blockL_def]
    norm_num
  map_one_left x := by
    apply Subtype.ext
    refine Prod.ext rfl ?_
    show conjNormalize (rotSq e ((((1 : I) : ℝ))) x) (blockL ι κ (L x)) = blockR ι κ (L' x)
    rw [conjNormalize_def, trace_rotSq_conj e hL, rotSq_conj, blockR_def]
    norm_num

/-- **Isomorphic line bundles have homotopic classifying maps**, after the
block embeddings into `ℂ^ι ⊕ ℂ^κ`.  This is what makes `e(L) := f_L^* h` a
function of the isomorphism class. -/
theorem homotopic_classL_classR (e : BundleIso L L') (hL : ∀ x, (L x).trace = 1) :
    (classL κ L hL).Homotopic
      (classR ι L' (fun x => by rw [trace_of_iso e x]; exact hL x)) :=
  ⟨rotHomotopy e hL⟩

end Rotation

end Bundle

end CharClass
end GroupApproximation
