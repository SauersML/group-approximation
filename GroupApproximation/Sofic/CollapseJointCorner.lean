import GroupApproximation.Sofic.ExactInvolutionLifts

/-!
# Step 1 of the involutive collapse, run along the joint corner

This file certifies Step 1 of a six-step proof sketch of `\ref{thm:collapse}`
(*involutive collapse*) that `non_mf_groups_exist.tex` used to print in
`\ref{subsec:collapse}`, and specifically its sentence

> "block compression along the finite commutative corner structure of the
> previously corrected microstates preserves exact commutation"

**That sketch is no longer printed.**  Commit `3a45fa60` ("Editorial pass:
rewrite orbit collapse, cut what nothing uses") moved the collapse mechanism
inside the matrix corona: `\ref{thm:collapse}` is now three sentences of Fourier
idempotents reducing to `\ref{thm:projection-collapse}`, and the microstate
corrections, the rank pseudometric and the almost-cocycle estimate are all gone.
The module is kept because the mathematics is correct and other modules consume
it, but it transcribes a route the reader will not find; the divergence is what
the proof ledger records at `CO.19`--`CO.22`, and `docs/COLLAPSE_STEP_AUDIT.md`
is graded against the deleted text.  No badge is owed here.

The manuscript describes **one** compression, taken along the corner structure
of the *whole* previously corrected commuting family at once, followed by
**one** spectral rounding.  `Sofic/ExactInvolutionLifts.lean` instead corrects
one involution at a time (`involutionStep R v = cornerInvolutionCorrection
(involutionCut R) v`, iterated in
`exists_isExactInvolution_comm_of_isExactInvolution`), which forces a separate
"the step never leaves the commutant" lemma (`involutionStep_commutant`, with
no counterpart in the TeX) and accumulates the cost `(15 ^ card - 1) * η`.

Here the induction is run the way the manuscript describes it.  Three things
change, and all three are improvements:

* **One compression, one rounding.**  The compression along the joint corner is
  the composite `E_{i₁} ∘ ⋯ ∘ E_{iₘ}` of the block compressions along the
  individual two-block cuts — `E_R x = ∑_{b : Bool} (involutionCut R b) * x *
  (involutionCut R b) = (x + R x R) / 2` (`cornerCompression_involutionCut`) —
  and the two-block compressions along commuting involutions compose to the
  compression along their joint corner.  The spectral sign is taken once, at
  the end, of the already self-adjoint compressed matrix.
* **No commutant lemma.**  The compressed matrix commutes with *every* member
  of the family simultaneously, so there are no earlier commutations to
  preserve; `involutionStep_commutant` has no role on this route.
* **Linear cost, and no smallness hypothesis.**  Each of the `m` block
  averages moves `v` by at most `η / 2`, and each is a contraction, so the
  compression moves `v` by at most `m η / 2`; the spectral rounding then costs
  at most `‖C * C - 1‖ ≤ 2 ‖C - v‖`.  The total is `3/2 * m * η` — linear in
  the size of the family, against `15 ^ m` for the iterated route — and no
  hypothesis of the form `15 ^ m * η ≤ 1` is needed anywhere, because the
  rounding estimate `norm_signOfHermitian_sub_le` is unconditional.

Nothing in `Sofic/ExactInvolutionLifts.lean` is modified: the two-block
development stays, and this file only adds the joint-corner route.
-/

namespace GroupApproximation
namespace CollapseJointCorner

open Matrix
open KazhdanCornerMatrices
open ExactInvolutionLifts
open scoped Matrix.Norms.L2Operator

variable {Y : Type*} [Fintype Y] [DecidableEq Y]
variable {ι : Type*}

/-! ## The block average along one two-block cut

Compression along the two spectral cuts of a single exact involution is the
average of the identity with conjugation by that involution.  Writing it in
closed form is what makes the joint compression a *composite* of elementary
compressions rather than an unanalysed `2 ^ m`-fold sum. -/

/-- The block compression of `x` along the two-block corner cut of `R`, in
closed form: the average of `x` with its conjugate by `R`. -/
noncomputable def blockAverage (R x : Matrix Y Y ℂ) : Matrix Y Y ℂ :=
  (2 : ℂ)⁻¹ • (x + R * x * R)

/-- **The block average is a corner compression.**  It is exactly
`cornerCompression` along the Bool-indexed pair of affine cuts of `R`, with no
hypothesis on `R` at all. -/
theorem cornerCompression_involutionCut (R x : Matrix Y Y ℂ) :
    cornerCompression (involutionCut R) x = blockAverage R x := by
  have hsandwich : ∀ (a b : ℂ) (S T : Matrix Y Y ℂ),
      (a • S) * x * (b • T) = (a * b) • (S * x * T) := by
    intro a b S T
    rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [cornerCompression, Fintype.sum_bool]
  simp only [involutionCut, affineCut, blockAverage]
  rw [hsandwich, hsandwich, ← smul_add]
  have hprod : (1 + -R) * x * (1 + -R) + (1 + R) * x * (1 + R)
      = (2 : ℂ) • (x + R * x * R) := by
    have hexp : (1 + -R) * x * (1 + -R) + (1 + R) * x * (1 + R)
        = x + x + R * x * R + R * x * R := by noncomm_ring
    rw [hexp]
    module
  rw [hprod, smul_smul, show ((2 : ℂ)⁻¹ * 2⁻¹ * 2) = (2 : ℂ)⁻¹ by norm_num]

/-- The block average is linear in its argument. -/
theorem blockAverage_sub (R x y : Matrix Y Y ℂ) :
    blockAverage R x - blockAverage R y = blockAverage R (x - y) := by
  have hinner : (x + R * x * R) - (y + R * y * R)
      = (x - y) + R * (x - y) * R := by noncomm_ring
  rw [blockAverage, blockAverage, blockAverage, ← smul_sub, hinner]

/-- The block average along a contraction is a contraction. -/
theorem norm_blockAverage_le {R : Matrix Y Y ℂ} (hR : ‖R‖ ≤ 1) (x : Matrix Y Y ℂ) :
    ‖blockAverage R x‖ ≤ ‖x‖ := by
  have hprod : ‖R * x * R‖ ≤ ‖x‖ :=
    calc ‖R * x * R‖ ≤ ‖R * x‖ * ‖R‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ ‖R * x‖ * 1 := mul_le_mul_of_nonneg_left hR (norm_nonneg _)
      _ = ‖R * x‖ := mul_one _
      _ ≤ ‖R‖ * ‖x‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hR (norm_nonneg _)
      _ = ‖x‖ := one_mul _
  have hsum : ‖x + R * x * R‖ ≤ ‖x‖ + ‖R * x * R‖ := norm_add_le _ _
  have hscalar : ‖((2 : ℂ)⁻¹)‖ = (1 / 2 : ℝ) := by norm_num
  rw [blockAverage, norm_smul, hscalar]
  linarith

/-- **The elementary cost of one compression.**  Compressing along the
two-block cut of an exact involution `R` moves `x` by at most half the
commutation defect of `x` against `R`. -/
theorem norm_blockAverage_sub_self {R : Matrix Y Y ℂ} (hR : IsExactInvolution R)
    (x : Matrix Y Y ℂ) :
    ‖blockAverage R x - x‖ ≤ (1 / 2 : ℝ) * ‖R * x - x * R‖ := by
  have hfactor : R * x * R - x = (R * x - x * R) * R := by
    calc R * x * R - x = R * x * R - x * (R * R) := by rw [hR.2, Matrix.mul_one]
      _ = (R * x - x * R) * R := by noncomm_ring
  have hstep : blockAverage R x - x = (2 : ℂ)⁻¹ • (R * x * R - x) := by
    rw [blockAverage]
    module
  have hnorm : ‖R * x * R - x‖ ≤ ‖R * x - x * R‖ := by
    rw [hfactor]
    calc ‖(R * x - x * R) * R‖ ≤ ‖R * x - x * R‖ * ‖R‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ ‖R * x - x * R‖ * 1 :=
        mul_le_mul_of_nonneg_left hR.norm_le_one (norm_nonneg _)
      _ = ‖R * x - x * R‖ := mul_one _
  have hscalar : ‖((2 : ℂ)⁻¹)‖ = (1 / 2 : ℝ) := by norm_num
  rw [hstep, norm_smul, hscalar]
  linarith

omit [DecidableEq Y] in
/-- The block average of a self-adjoint matrix along a self-adjoint involution
is self-adjoint. -/
theorem blockAverage_conjTranspose {R x : Matrix Y Y ℂ} (hR : Rᴴ = R) (hx : xᴴ = x) :
    (blockAverage R x)ᴴ = blockAverage R x := by
  have hstar : star ((2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ := by norm_num
  rw [blockAverage, Matrix.conjTranspose_smul, hstar, Matrix.conjTranspose_add,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hR, hx, mul_assoc]

/-- **The compression lands in the commutant of the involution it compresses
along.**  This is the manuscript's "preserves exact commutation", for the
member being compressed against, and it needs no hypothesis on `x`. -/
theorem blockAverage_comm_self {R : Matrix Y Y ℂ} (hR : IsExactInvolution R)
    (x : Matrix Y Y ℂ) : R * blockAverage R x = blockAverage R x * R := by
  have h1 : R * (R * x * R) = x * R := by
    calc R * (R * x * R) = (R * R) * x * R := by noncomm_ring
      _ = x * R := by rw [hR.2]; noncomm_ring
  have h2 : (R * x * R) * R = R * x := by
    calc (R * x * R) * R = R * x * (R * R) := by noncomm_ring
      _ = R * x := by rw [hR.2]; noncomm_ring
  have key : R * (x + R * x * R) = (x + R * x * R) * R := by
    calc R * (x + R * x * R) = R * x + R * (R * x * R) := by noncomm_ring
      _ = R * x + x * R := by rw [h1]
      _ = (R * x * R) * R + x * R := by rw [h2]
      _ = (x + R * x * R) * R := by noncomm_ring
  rw [blockAverage, Matrix.mul_smul, Matrix.smul_mul, key]

/-- **The compression preserves commutations already in force.**  Anything
commuting with both `R` and `x` still commutes with the block average.  On the
joint-corner route this is used only to carry commutation with the *other*
members of the family through one elementary compression; it is not an
induction hypothesis about the corrected object, so it is not the
`involutionStep_commutant` of the two-block route. -/
theorem blockAverage_comm_of_comm {R S x : Matrix Y Y ℂ}
    (hSR : S * R = R * S) (hSx : S * x = x * S) :
    S * blockAverage R x = blockAverage R x * S := by
  have key : S * (x + R * x * R) = (x + R * x * R) * S := by
    calc S * (x + R * x * R) = S * x + (S * R) * x * R := by noncomm_ring
      _ = x * S + (R * S) * x * R := by rw [hSx, hSR]
      _ = x * S + R * (S * x) * R := by noncomm_ring
      _ = x * S + R * (x * S) * R := by rw [hSx]
      _ = x * S + R * x * (S * R) := by noncomm_ring
      _ = x * S + R * x * (R * S) := by rw [hSR]
      _ = (x + R * x * R) * S := by noncomm_ring
  rw [blockAverage, Matrix.mul_smul, Matrix.smul_mul, key]

/-! ## Compression along the joint corner of a finite family

The joint corner structure of a finite family of commuting exact involutions
`R i`, `i ∈ l`, is the finite commutative algebra they generate; its minimal
projections are the joint spectral blocks, and compression along it is the
composite of the compressions along the individual cuts.  That composite is
`jointCompression`; `Sofic/CollapseJointCornerRefinement.lean` proves that
composing two commuting corner compressions is again a corner compression, so
`jointCompression R l` is the corner compression along a genuine (at most
`2 ^ l.length`-block) corner partition. -/

/-- Block compression of `x` along the joint corner structure of the family
`R i`, `i ∈ l`. -/
noncomputable def jointCompression (R : ι → Matrix Y Y ℂ) (l : List ι)
    (x : Matrix Y Y ℂ) : Matrix Y Y ℂ :=
  l.foldr (fun i y ↦ blockAverage (R i) y) x

omit [DecidableEq Y] in
@[simp]
theorem jointCompression_nil (R : ι → Matrix Y Y ℂ) (x : Matrix Y Y ℂ) :
    jointCompression R [] x = x := rfl

omit [DecidableEq Y] in
@[simp]
theorem jointCompression_cons (R : ι → Matrix Y Y ℂ) (i : ι) (l : List ι)
    (x : Matrix Y Y ℂ) :
    jointCompression R (i :: l) x = blockAverage (R i) (jointCompression R l x) :=
  rfl

/-- The joint compression is a contraction. -/
theorem norm_jointCompression_le {R : ι → Matrix Y Y ℂ} (hR : ∀ i, ‖R i‖ ≤ 1)
    (l : List ι) (x : Matrix Y Y ℂ) : ‖jointCompression R l x‖ ≤ ‖x‖ := by
  induction l with
  | nil => simp
  | cons i l ih =>
      rw [jointCompression_cons]
      exact (norm_blockAverage_le (hR i) _).trans ih

/-- The joint compression is `1`-Lipschitz. -/
theorem norm_jointCompression_sub_jointCompression {R : ι → Matrix Y Y ℂ}
    (hR : ∀ i, ‖R i‖ ≤ 1) (l : List ι) (x y : Matrix Y Y ℂ) :
    ‖jointCompression R l x - jointCompression R l y‖ ≤ ‖x - y‖ := by
  induction l with
  | nil => simp
  | cons i l ih =>
      rw [jointCompression_cons, jointCompression_cons, blockAverage_sub]
      exact (norm_blockAverage_le (hR i) _).trans ih

/-- **The joint compression costs linearly in the size of the family.**  The
`m` elementary block averages each move `v` by at most `η / 2`, and each is a
contraction, so the errors add instead of compounding. -/
theorem norm_jointCompression_sub_self {R : ι → Matrix Y Y ℂ}
    (hR : ∀ i, IsExactInvolution (R i)) {v : Matrix Y Y ℂ} {η : ℝ}
    (l : List ι) :
    (∀ i ∈ l, ‖R i * v - v * R i‖ ≤ η) →
      ‖jointCompression R l v - v‖ ≤ (l.length : ℝ) * (η / 2) := by
  induction l with
  | nil =>
      intro _
      simp
  | cons i l ih =>
      intro hcomm
      have hIH : ‖jointCompression R l v - v‖ ≤ (l.length : ℝ) * (η / 2) :=
        ih fun j hj ↦ hcomm j (List.mem_cons_of_mem i hj)
      have hhead : ‖blockAverage (R i) v - v‖ ≤ η / 2 := by
        have h := norm_blockAverage_sub_self (hR i) v
        have h2 := hcomm i (by simp)
        linarith
      have hstep : ‖blockAverage (R i) (jointCompression R l v) -
          blockAverage (R i) v‖ ≤ ‖jointCompression R l v - v‖ := by
        rw [blockAverage_sub]
        exact norm_blockAverage_le (hR i).norm_le_one _
      have hsplit : blockAverage (R i) (jointCompression R l v) - v =
          (blockAverage (R i) (jointCompression R l v) - blockAverage (R i) v) +
            (blockAverage (R i) v - v) := by abel
      have htri : ‖blockAverage (R i) (jointCompression R l v) - v‖ ≤
          ‖blockAverage (R i) (jointCompression R l v) - blockAverage (R i) v‖ +
            ‖blockAverage (R i) v - v‖ := by
        rw [hsplit]
        exact norm_add_le _ _
      have hlen : ((i :: l).length : ℝ) = (l.length : ℝ) + 1 := by simp
      rw [jointCompression_cons, hlen]
      linarith

/-- **The joint compression lands in the commutant of the whole family.**  No
commutation has to be re-established afterwards: the single compression
achieves all of them simultaneously. -/
theorem jointCompression_comm {R : ι → Matrix Y Y ℂ}
    (hR : ∀ i, IsExactInvolution (R i))
    (hRcomm : ∀ i j, R i * R j = R j * R i) (l : List ι) (x : Matrix Y Y ℂ) :
    ∀ j ∈ l, R j * jointCompression R l x = jointCompression R l x * R j := by
  induction l with
  | nil =>
      intro j hj
      simp at hj
  | cons i l ih =>
      intro j hj
      rw [jointCompression_cons]
      rcases List.mem_cons.mp hj with hji | hj'
      · rw [hji]
        exact blockAverage_comm_self (hR i) _
      · exact blockAverage_comm_of_comm (hRcomm j i) (ih j hj')

/-- The joint compression of a self-adjoint matrix is self-adjoint, so the
spectral sign can be taken directly, with no symmetrization step. -/
theorem jointCompression_conjTranspose {R : ι → Matrix Y Y ℂ}
    (hR : ∀ i, IsExactInvolution (R i)) {x : Matrix Y Y ℂ} (hx : xᴴ = x)
    (l : List ι) : (jointCompression R l x)ᴴ = jointCompression R l x := by
  induction l with
  | nil => exact hx
  | cons i l ih => exact blockAverage_conjTranspose (hR i).1 ih

/-! ## The corrected involution

One spectral rounding, applied once to the compressed matrix. -/

omit [Fintype Y] [DecidableEq Y] in
/-- The Hermitian part of a self-adjoint matrix is the matrix itself. -/
theorem hermitianPart_of_selfAdjoint {x : Matrix Y Y ℂ} (hx : xᴴ = x) :
    ApproxInvolutionCorner.hermitianPart x = x := by
  rw [ApproxInvolutionCorner.hermitianPart, hx]
  module

/-- **Rounding a self-adjoint contraction.**  If `C` is self-adjoint with
`‖C‖ ≤ 1` and `v` is an exact involution, the spectral sign of `C` is an exact
involution within `3 ‖C - v‖` of `v`.  No smallness hypothesis is needed: the
rounding estimate `norm_signOfHermitian_sub_le` is unconditional and the
involution defect of `C` is controlled by `‖C * C - v * v‖ ≤ 2 ‖C - v‖`. -/
theorem norm_exactInvolutionCorrection_sub_le_of_selfAdjoint {C v : Matrix Y Y ℂ}
    (hC : Cᴴ = C) (hCnorm : ‖C‖ ≤ 1) (hv : IsExactInvolution v) :
    ‖exactInvolutionCorrection C - v‖ ≤ 3 * ‖C - v‖ := by
  have hHP : ApproxInvolutionCorner.hermitianPart C = C :=
    hermitianPart_of_selfAdjoint hC
  have hround : ‖exactInvolutionCorrection C -
      ApproxInvolutionCorner.hermitianPart C‖ ≤
      ‖ApproxInvolutionCorner.hermitianPart C *
        ApproxInvolutionCorner.hermitianPart C - 1‖ :=
    norm_signOfHermitian_sub_le (ApproxInvolutionCorner.hermitianPart C)
      (ApproxInvolutionCorner.hermitianPart_isHermitian C)
  rw [hHP] at hround
  have hsq : ‖C * C - 1‖ ≤ 2 * ‖C - v‖ := by
    have hdecomp : C * C - 1 = C * (C - v) + (C - v) * v := by
      calc C * C - 1 = C * C - v * v := by rw [hv.2]
        _ = C * (C - v) + (C - v) * v := by noncomm_ring
    have h1 : ‖C * (C - v)‖ ≤ ‖C‖ * ‖C - v‖ := Matrix.l2_opNorm_mul _ _
    have h2 : ‖(C - v) * v‖ ≤ ‖C - v‖ * ‖v‖ := Matrix.l2_opNorm_mul _ _
    have h3 : ‖C * (C - v) + (C - v) * v‖ ≤
        ‖C * (C - v)‖ + ‖(C - v) * v‖ := norm_add_le _ _
    have h4 : (0 : ℝ) ≤ ‖C - v‖ := norm_nonneg _
    have h5 : ‖v‖ ≤ 1 := hv.norm_le_one
    have h6 : (0 : ℝ) ≤ ‖C - v‖ * (1 - ‖C‖) :=
      mul_nonneg h4 (sub_nonneg.mpr hCnorm)
    have h7 : (0 : ℝ) ≤ ‖C - v‖ * (1 - ‖v‖) :=
      mul_nonneg h4 (sub_nonneg.mpr h5)
    rw [hdecomp]
    nlinarith [h1, h2, h3, h6, h7]
  have hsplit : exactInvolutionCorrection C - v =
      (exactInvolutionCorrection C - C) + (C - v) := by abel
  have htri : ‖exactInvolutionCorrection C - v‖ ≤
      ‖exactInvolutionCorrection C - C‖ + ‖C - v‖ := by
    rw [hsplit]
    exact norm_add_le _ _
  linarith

/-- The joint-corner correction of `v`: the spectral sign of the compression of
`v` along the joint corner structure of the family `R i`, `i ∈ l`. -/
noncomputable def jointInvolutionCorrection (R : ι → Matrix Y Y ℂ) (l : List ι)
    (v : Matrix Y Y ℂ) : Matrix Y Y ℂ :=
  exactInvolutionCorrection (jointCompression R l v)

/-- The joint-corner correction is an exact involution, for every `R`, `l`,
`v`. -/
theorem jointInvolutionCorrection_isExactInvolution (R : ι → Matrix Y Y ℂ)
    (l : List ι) (v : Matrix Y Y ℂ) :
    IsExactInvolution (jointInvolutionCorrection R l v) :=
  exactInvolutionCorrection_isExactInvolution _

/-- The joint-corner correction commutes **exactly** with every member of the
family, simultaneously. -/
theorem jointInvolutionCorrection_comm {R : ι → Matrix Y Y ℂ}
    (hR : ∀ i, IsExactInvolution (R i)) (hRcomm : ∀ i j, R i * R j = R j * R i)
    {v : Matrix Y Y ℂ} (hv : IsExactInvolution v) (l : List ι) :
    ∀ j ∈ l, jointInvolutionCorrection R l v * R j =
      R j * jointInvolutionCorrection R l v := by
  intro j hj
  have hH : (jointCompression R l v)ᴴ = jointCompression R l v :=
    jointCompression_conjTranspose hR hv.1 l
  have hHP : ApproxInvolutionCorner.hermitianPart (jointCompression R l v) =
      jointCompression R l v := hermitianPart_of_selfAdjoint hH
  have hcomm : R j * ApproxInvolutionCorner.hermitianPart
      (jointCompression R l v) =
      ApproxInvolutionCorner.hermitianPart (jointCompression R l v) * R j := by
    rw [hHP]
    exact jointCompression_comm hR hRcomm l v j hj
  exact (commute_signOfHermitian_of_commute
    (ApproxInvolutionCorner.hermitianPart (jointCompression R l v))
    (ApproxInvolutionCorner.hermitianPart_isHermitian _) hcomm).symm

/-- **The joint-corner Step 1 estimate.**  Correcting an exact involution `v`
against a commuting family of `m` exact involutions, all at commutation defect
at most `η`, costs at most `3/2 * m * η`.  Compare
`ExactInvolutionLifts.exists_isExactInvolution_comm_of_isExactInvolution`,
whose iterated two-block route costs `(15 ^ m - 1) * η` and needs
`15 ^ m * η ≤ 1`; here there is no side condition at all. -/
theorem norm_jointInvolutionCorrection_sub_le {R : ι → Matrix Y Y ℂ}
    (hR : ∀ i, IsExactInvolution (R i)) {v : Matrix Y Y ℂ}
    (hv : IsExactInvolution v) {η : ℝ} (l : List ι)
    (hcomm : ∀ i ∈ l, ‖R i * v - v * R i‖ ≤ η) :
    ‖jointInvolutionCorrection R l v - v‖ ≤ 3 / 2 * (l.length : ℝ) * η := by
  have hCv : ‖jointCompression R l v - v‖ ≤ (l.length : ℝ) * (η / 2) :=
    norm_jointCompression_sub_self hR l hcomm
  have hCnorm : ‖jointCompression R l v‖ ≤ 1 :=
    (norm_jointCompression_le (fun i ↦ (hR i).norm_le_one) l v).trans
      hv.norm_le_one
  have hCherm : (jointCompression R l v)ᴴ = jointCompression R l v :=
    jointCompression_conjTranspose hR hv.1 l
  have hround : ‖jointInvolutionCorrection R l v - v‖ ≤
      3 * ‖jointCompression R l v - v‖ :=
    norm_exactInvolutionCorrection_sub_le_of_selfAdjoint hCherm hCnorm hv
  linarith

/-! ## The manuscript's Step 1 induction, over a finite window -/

/-- **Step 1 of `thm:collapse`, joint-corner form.**  An exact involution `v`
almost commuting with a finite commuting family of exact involutions is
corrected, by a *single* compression along the joint corner structure of the
family followed by a *single* spectral rounding, into an exact involution
commuting exactly with every member.

The cost `3/2 * s.card * η` is **linear** in the size of the family, and there
is no smallness hypothesis.  The iterated two-block route
`ExactInvolutionLifts.exists_isExactInvolution_comm_of_isExactInvolution`
proves the same statement with cost `(15 ^ s.card - 1) * η` under the side
condition `15 ^ s.card * η ≤ 1`. -/
theorem exists_isExactInvolution_comm_of_isExactInvolution_joint
    (R : ι → Matrix Y Y ℂ) (hR : ∀ i, IsExactInvolution (R i))
    (hRcomm : ∀ i j, R i * R j = R j * R i) (s : Finset ι)
    {v : Matrix Y Y ℂ} (hv : IsExactInvolution v) {η : ℝ}
    (hcomm : ∀ i ∈ s, ‖R i * v - v * R i‖ ≤ η) :
    ∃ W : Matrix Y Y ℂ, IsExactInvolution W ∧ (∀ i ∈ s, W * R i = R i * W) ∧
      ‖W - v‖ ≤ 3 / 2 * (s.card : ℝ) * η := by
  refine ⟨jointInvolutionCorrection R s.toList v,
    jointInvolutionCorrection_isExactInvolution R s.toList v, ?_, ?_⟩
  · intro i hi
    exact jointInvolutionCorrection_comm hR hRcomm hv s.toList i
      (Finset.mem_toList.mpr hi)
  · have h := norm_jointInvolutionCorrection_sub_le hR hv (η := η) s.toList
      (fun i hi ↦ hcomm i (Finset.mem_toList.mp hi))
    rwa [Finset.length_toList] at h

/-- **Step 1 of `thm:collapse` from the raw microstates, joint-corner form.**
A unitary `u` with involution defect at most `ε` and commutation defect at most
`ε` against each of `m` commuting exact involutions lies within
`(9/2 * m + 1) * ε` of an exact involution commuting exactly with all of them.

The corresponding two-block statement,
`ExactInvolutionLifts.exists_isExactInvolution_comm_of_unitary`, gives
`3 * 15 ^ m * ε` under the side condition `15 ^ m * (3 * ε) ≤ 1`. -/
theorem exists_isExactInvolution_comm_of_unitary_joint
    (R : ι → Matrix Y Y ℂ) (hR : ∀ i, IsExactInvolution (R i))
    (hRcomm : ∀ i j, R i * R j = R j * R i) (s : Finset ι)
    {u : Matrix Y Y ℂ} (hu : u ∈ Matrix.unitaryGroup Y ℂ) {ε : ℝ}
    (hinv : ‖u * u - 1‖ ≤ ε)
    (hcomm : ∀ i ∈ s, ‖R i * u - u * R i‖ ≤ ε) :
    ∃ W : Matrix Y Y ℂ, IsExactInvolution W ∧ (∀ i ∈ s, W * R i = R i * W) ∧
      ‖W - u‖ ≤ (9 / 2 * (s.card : ℝ) + 1) * ε := by
  have hvd : ‖exactInvolutionCorrection u - u‖ ≤ ε :=
    (norm_exactInvolutionCorrection_sub_le u hu).trans hinv
  have hvcomm : ∀ i ∈ s, ‖R i * exactInvolutionCorrection u -
      exactInvolutionCorrection u * R i‖ ≤ 3 * ε := by
    intro i hi
    have h := norm_comm_sub_le_of_norm_sub_le (hR i) (hcomm i hi) hvd
    linarith
  obtain ⟨W, hW, hWcomm, hWd⟩ :=
    exists_isExactInvolution_comm_of_isExactInvolution_joint R hR hRcomm s
      (exactInvolutionCorrection_isExactInvolution u) hvcomm
  refine ⟨W, hW, hWcomm, ?_⟩
  have hsplit : W - u =
      (W - exactInvolutionCorrection u) + (exactInvolutionCorrection u - u) := by
    abel
  have htri : ‖W - u‖ ≤
      ‖W - exactInvolutionCorrection u‖ + ‖exactInvolutionCorrection u - u‖ := by
    rw [hsplit]
    exact norm_add_le _ _
  calc ‖W - u‖ ≤ 3 / 2 * (s.card : ℝ) * (3 * ε) + ε := by linarith
    _ = (9 / 2 * (s.card : ℝ) + 1) * ε := by ring

/-- A rounder form of `exists_isExactInvolution_comm_of_unitary_joint`, shaped
for the window induction of `InvolutionOrbitMicrostates.exists_family_on`:
choosing `ε₀ = ε / (5 * (F.card + 1))` makes the output tolerance exactly `ε`,
with no clamp and no smallness hypothesis. -/
theorem exists_isExactInvolution_comm_of_unitary_joint'
    (R : ι → Matrix Y Y ℂ) (hR : ∀ i, IsExactInvolution (R i))
    (hRcomm : ∀ i j, R i * R j = R j * R i) (s : Finset ι)
    {u : Matrix Y Y ℂ} (hu : u ∈ Matrix.unitaryGroup Y ℂ) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hinv : ‖u * u - 1‖ ≤ ε)
    (hcomm : ∀ i ∈ s, ‖R i * u - u * R i‖ ≤ ε) :
    ∃ W : Matrix Y Y ℂ, IsExactInvolution W ∧ (∀ i ∈ s, W * R i = R i * W) ∧
      ‖W - u‖ ≤ 5 * ((s.card : ℝ) + 1) * ε := by
  obtain ⟨W, hW, hWcomm, hWd⟩ :=
    exists_isExactInvolution_comm_of_unitary_joint R hR hRcomm s hu hinv hcomm
  refine ⟨W, hW, hWcomm, hWd.trans ?_⟩
  have hcard0 : (0 : ℝ) ≤ (s.card : ℝ) := Nat.cast_nonneg _
  nlinarith [mul_nonneg hcard0 hε0]

end CollapseJointCorner
end GroupApproximation
