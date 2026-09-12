import GroupApproximation.Manuscript.OneSidedMFRadical.RankDescentPrintedLemmas
import GroupApproximation.Manuscript.OneSidedMFRadical.RankFourCompressionCellPrinted
import GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingSentences
import GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingSimple
import GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingProperIsometry
import GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingStrictness
import GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingUnconditional
import GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingMaximal
import GroupApproximation.Manuscript.OneSidedMFRadical.UnitGroupRankDescent
import GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingEJZUnconditional
import GroupApproximation.Meta.AxiomGuard

/-!
# Sentence-level formalization of `non_mf_groups_exist.tex`, `sec:one-sided-inverses`

`non_mf_groups_exist.tex`, Section "One-sided inverses and elementary
groups": the proofs of Lemma `lem:two-copies`, Lemma `lem:rank-two`, Lemma
`lem:ring-compression-cell`, Theorem `thm:full-defect-ring`, Corollary
`cor:simple-infinite-ring` and Corollary `cor:one-sided-ring-maximal`.

The proof of `thm:full-defect-ring` itself is already carried, sentence by
sentence, in `Manuscript/OneSidedMFRadical/FullDefectRingSentences.lean`
(landed on `origin/main`); nothing there is repeated here.  This module
covers what is not yet carried: the section-opening prose, the two new rank
lemmas' proofs, the rank-four compression cell's proof (statement now closed
by `RankFourCompressionCellPrinted`), and the two corollaries' proofs.

Every carrier below is a restatement of an already-landed lemma, at the
generality the printed sentence itself asks for (an arbitrary unital ring,
not the specific universal ring `𝒞` that `thm:full-defect-ring`'s own proof
runs at).  Nothing is proved twice: the underlying mathematics is
`GroupApproximation.RankDescent` (`RankDescentEmbedding.lean`,
`ProperlyInfiniteUnit.lean`, `RankTwoNormalGeneration.lean`) and
`GroupApproximation.Manuscript.OneSidedMFRadical.RankFourCompressionCellPrinted`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMFSentences
namespace OneSidedSentences

open GroupApproximation.RankDescent
open GroupApproximation.OneSidedCompressor
open GroupApproximation.Manuscript.OneSidedMFRadical.RankFourCompressionCellPrinted
open GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingSentences
open GroupApproximation.Manuscript.OneSidedMFRadical.RankDescentPrinted
open scoped commutatorElement

/-! ## Lemma `lem:two-copies`, the proof -/

section TwoCopies

variable {R : Type} [Ring R] (P : OneSidedInverse R)

/-- **`lem:two-copies`, proof sentence 1.**

> Put `e = 1 - st`, so that `es = te = 0`, and choose `aⱼ, bⱼ ∈ R`,
> `0 ≤ j < m`, with `∑ⱼ aⱼ e bⱼ = 1`.

The defining equation for `e` is `OneSidedInverse.e_eq`; the two vanishing
products are `OneSidedInverse.e_mul_s` and `OneSidedInverse.t_mul_e`.  The
choice of `aⱼ, bⱼ` is the fullness hypothesis, carried as the bound variable
`hab` below rather than restated. -/
theorem manuscriptSentence_twoCopiesSetup :
    P.e = 1 - P.s * P.t ∧ P.e * P.s = 0 ∧ P.t * P.e = 0 :=
  ⟨P.e_eq, P.e_mul_s, P.t_mul_e⟩

variable {m : ℕ} (a b : Fin m → R) (hab : ∑ k, a k * P.e * b k = 1)

/-- **`lem:two-copies`, proof sentence 2.**

> Put `v₀ = sᵐ`, `w₀ = tᵐ`, `v₁ = ∑ⱼ sʲ e bⱼ`, `w₁ = ∑ⱼ aⱼ e tʲ`.

Definitional: these are exactly the four fields of `RankDescent.ofFull`. -/
theorem manuscriptSentence_twoCopiesDefine :
    (ofFull P a b hab).v = ![P.s ^ m, ∑ k : Fin m, P.s ^ (k : ℕ) * P.e * b k] ∧
      (ofFull P a b hab).w =
        ![P.t ^ m, ∑ k : Fin m, a k * P.e * P.t ^ (k : ℕ)] :=
  ⟨rfl, rfl⟩

include hab in
/-- **`lem:two-copies`, proof sentence 5.**

> So `w₀v₀ = tᵐsᵐ = 1`, `w₁v₁ = ∑ⱼ aⱼ e bⱼ = 1`, `w₀v₁ = ∑ⱼ t^{m-j} e bⱼ = 0`,
> and `w₁v₀ = ∑ⱼ aⱼ e s^{m-j} = 0`.

The four printed equations, in the printed order: `full_w0_mul_v0`,
`full_w1_mul_v1`, `full_w0_mul_v1`, `full_w1_mul_v0`. -/
theorem manuscriptSentence_twoCopiesFourEquations :
    P.t ^ m * P.s ^ m = 1 ∧
      (∑ k : Fin m, a k * P.e * P.t ^ (k : ℕ)) *
          (∑ k : Fin m, P.s ^ (k : ℕ) * P.e * b k) = 1 ∧
      P.t ^ m * (∑ k : Fin m, P.s ^ (k : ℕ) * P.e * b k) = 0 ∧
      (∑ k : Fin m, a k * P.e * P.t ^ (k : ℕ)) * P.s ^ m = 0 :=
  ⟨full_w0_mul_v0 P, full_w1_mul_v1 P a b hab, full_w0_mul_v1 P b,
    full_w1_mul_v0 P a⟩

end TwoCopies

/-- **`lem:two-copies`, proof sentence 4.**

> For all `i, j ≥ 0`, `e tⁱ sʲ e = δᵢⱼ e`: for `j > i` the middle factor is
> `s^{j-i}`, which `e` kills on the left, and for `i > j` it is `t^{i-j}`,
> which `e` kills on the right.

`e_mul_t_pow_mul_s_pow_mul_e`, at every natural `i, j` and not only those
below the fullness witness count `m`. -/
theorem manuscriptSentence_twoCopiesOrthogonality {R : Type} [Ring R]
    (P : OneSidedInverse R) (i j : ℕ) :
    P.e * P.t ^ i * P.s ^ j * P.e = if i = j then P.e else 0 :=
  e_mul_t_pow_mul_s_pow_mul_e P i j

/-- **`lem:two-copies`, proof sentence 6 (the converse).**

> Conversely, `w₁(1-v₀w₀)v₁ = w₁v₁ - (w₁v₀)(w₀v₁) = 1`.

Stated for arbitrary `v, w : Fin 2 → R` with the printed orthogonality
`wᵢvⱼ = δᵢⱼ`, matching the converse direction of `lem:two-copies` at its own
generality (not tied to the `ofFull` construction).  This is the same
computation as `ProperlyInfiniteUnit.w_one_mul_e_mul_v_one`, run directly off
the bare orthogonality hypothesis instead of the bundled structure. -/
theorem manuscriptSentence_twoCopiesConverse {R : Type} [Ring R]
    (v w : Fin 2 → R) (hvw : ∀ i j, w i * v j = if i = j then 1 else 0) :
    w 1 * (1 - v 0 * w 0) * v 1 = w 1 * v 1 - (w 1 * v 0) * (w 0 * v 1) ∧
      w 1 * (1 - v 0 * w 0) * v 1 = 1 := by
  have hne : (1 : Fin 2) ≠ 0 := by decide
  have h10 : w 1 * v 0 = 0 := by simpa [hne] using hvw 1 0
  have h11 : w 1 * v 1 = 1 := by simpa using hvw 1 1
  refine ⟨by noncomm_ring, ?_⟩
  have key : w 1 * (1 - v 0 * w 0) * v 1
      = w 1 * v 1 - w 1 * v 0 * (w 0 * v 1) := by noncomm_ring
  rw [key, h10, h11]
  simp

/-! ## Lemma `lem:rank-two`, the proof -/

/-- A general group-theoretic fact used implicitly at the start of the
printed proof: every commutator of the normal-closure generator with an
arbitrary element already lies in that normal closure.  (Internal step
`hcomm_mem` of `RankDescent.normalClosure_gen_eq_top`, extracted as its own
statement so later sentences can cite it directly.) -/
theorem commutator_mem_normalClosure_self {G : Type*} [Group G] (x g : G) :
    ⁅x, g⁆ ∈ Subgroup.normalClosure ({x} : Set G) := by
  set N := Subgroup.normalClosure ({x} : Set G) with hN
  haveI hNnormal : N.Normal := Subgroup.normalClosure_normal
  have hx : x ∈ N := Subgroup.subset_normalClosure rfl
  have hconj : g * x⁻¹ * g⁻¹ ∈ N := hNnormal.conj_mem _ (N.inv_mem hx) g
  have heq : ⁅x, g⁆ = x * (g * x⁻¹ * g⁻¹) := by rw [commutatorElement_def]; group
  rw [heq]
  exact N.mul_mem hx hconj

/-- **`lem:rank-two`, proof sentences 1-2.**

> The matrix `e₁₂(v)e₂₁(b)e₁₂(-v)` has rows `(1+vb, -vbv)` and `(b, 1-bv)`, so
> for `bv = 0` it is `(1+vb, 0; b, 1)`, and multiplying by `e₂₁(-b)` gives
> `D = diag(1+vb, 1)`.  Let `N` be the normal closure of `D` in `EL₂(R)`.

The final matrix value is `RankDescent.gen_val`; the row computation before
specializing to `bv = 0` is not separately named (the `fin_cases`-driven
proof of `gen_val` computes the product directly).  `D ∈ N` is definitional. -/
theorem manuscriptSentence_rankTwoGeneratorValueAndClosure {R : Type} [Ring R]
    (v b : R) (hbv : b * v = 0) :
    ((gen v b : (Matrix (Fin 2) (Fin 2) R)ˣ) : Matrix (Fin 2) (Fin 2) R)
        = 1 + Matrix.single 0 0 (v * b) ∧
      gen v b ∈
        Subgroup.normalClosure ({gen v b} : Set (elementaryGroup (Fin 2) R)) :=
  ⟨gen_val v b hbv, Subgroup.subset_normalClosure rfl⟩

/-- **`lem:rank-two`, proof sentence 3.**

> For `r ∈ R`, `[D, e₁₂(ar)] = e₁₂((1+vb)ar - ar) = e₁₂(vr)`, since `ba = 1`;
> so `e₁₂(vR) ≤ N`.

The commutator value is `RankDescent.gen_commutator_upperRoot_mul` (the
intermediate form `(1+vb)ar - ar` is folded into the same computation, not
separately named); membership in `N` is
`commutator_mem_normalClosure_self`. -/
theorem manuscriptSentence_rankTwoUpperRootInClosure {R : Type} [Ring R]
    (v a b : R) (hbv : b * v = 0) (hba : b * a = 1) (r : R) :
    ⁅gen v b, upperRoot (a * r)⁆ = upperRoot (v * r) ∧
      upperRoot (v * r) ∈
        Subgroup.normalClosure ({gen v b} : Set (elementaryGroup (Fin 2) R)) := by
  have hval := gen_commutator_upperRoot_mul v a b hbv hba r
  refine ⟨hval, ?_⟩
  rw [← hval]
  exact commutator_mem_normalClosure_self (gen v b) (upperRoot (a * r))

/-- **`lem:rank-two`, proof sentence 4.**

> Put `f = 1 - vw`, an idempotent with `fv = 0 = wf`, and
> `z = vf + fw + 1 - f - vfw`.

Definitional (`RankDescent.fIdem`, `RankDescent.zElt`), together with the
idempotence and annihilation facts `f_mul_f`, `f_mul_v`, `w_mul_f`. -/
theorem manuscriptSentence_rankTwoInvolutionSetup {R : Type} [Ring R]
    (v w : R) (hwv : w * v = 1) :
    fIdem v w = 1 - v * w ∧ fIdem v w * fIdem v w = fIdem v w ∧
      fIdem v w * v = 0 ∧ w * fIdem v w = 0 ∧
      zElt v w = v * fIdem v w + fIdem v w * w + 1 - fIdem v w - gIdem v w :=
  ⟨rfl, f_mul_f v w hwv, f_mul_v v w hwv, w_mul_f v w hwv, rfl⟩

/-- **`lem:rank-two`, proof sentences 5-6.**

> Put `x = vf`, `y = fw`, `q = vfw`, and `c = 1 - f - q`, so that `z = x+y+c`.
> From `wv = 1` and `fv = wf = 0`: ... so `z² = q + f + c = 1` and
> `zf = xf + yf + cf = vf`.

The decomposition `z = x + y + c` is `zElt_eq`; the multiplication-table
computations that give `z² = 1` are internal to
`RankDescent.zElt_mul_zElt`'s proof and are not separately named, but its
two conclusions -- exactly the printed final results `z² = 1` and `zf = vf`
-- are `zElt_mul_zElt` and `zElt_mul_fIdem`. -/
theorem manuscriptSentence_rankTwoInvolutionSquareAndFix {R : Type} [Ring R]
    (v w : R) (hwv : w * v = 1) :
    zElt v w = v * fIdem v w + fIdem v w * w + (1 - fIdem v w - gIdem v w) ∧
      zElt v w * zElt v w = 1 ∧ zElt v w * fIdem v w = v * fIdem v w :=
  ⟨zElt_eq v w, zElt_mul_zElt v w hwv, zElt_mul_fIdem v w hwv⟩

/-- **`lem:rank-two`, proof sentence 7.**

> The factorization `diag(z,z⁻¹) = e₁₂(z)e₂₁(-z⁻¹)e₁₂(z) · e₁₂(-1)e₂₁(1)e₁₂(-1)`
> puts `h = diag(z,z)` in `EL₂(R)`.

Since `z² = 1`, `z⁻¹ = z` and the printed six-transvection word is
`RankDescent.involutionDiag z`; membership in `EL₂(R)` is its type, and the
displayed value is `involutionDiag_val`. -/
theorem manuscriptSentence_rankTwoInvolutionDiag {R : Type} [Ring R]
    (v w : R) (hwv : w * v = 1) :
    ((involutionDiag (zElt v w) : (Matrix (Fin 2) (Fin 2) R)ˣ) :
        Matrix (Fin 2) (Fin 2) R) = !![zElt v w, 0; 0, zElt v w] :=
  involutionDiag_val (zElt v w) (zElt_mul_zElt v w hwv)

/-- **`lem:rank-two`, proof sentence 8.**

> and `h e₁₂(fr) h⁻¹ = e₁₂(zfrz) = e₁₂(v·frz) ∈ N`.

The conjugation value `e₁₂(zfrz)` is `involutionDiag_conj_upperRoot`; the
rewrite to `e₁₂(v·frz)` uses `zf = vf` (`zElt_mul_fIdem`); membership in `N`
is `manuscriptSentence_rankTwoUpperRootInClosure`, applied at the argument
`frz` instead of the generic printed `r` (that theorem already holds for
every element of `R`, matching what the printed sentence needs here). -/
theorem manuscriptSentence_rankTwoConjugateInClosure {R : Type} [Ring R]
    (v w a b : R) (hwv : w * v = 1) (hbv : b * v = 0) (hba : b * a = 1)
    (r : R) :
    involutionDiag (zElt v w) * upperRoot (fIdem v w * r) *
        (involutionDiag (zElt v w))⁻¹
        = upperRoot (v * (fIdem v w * r * zElt v w)) ∧
      upperRoot (v * (fIdem v w * r * zElt v w)) ∈
        Subgroup.normalClosure ({gen v b} : Set (elementaryGroup (Fin 2) R)) := by
  have hz : zElt v w * zElt v w = 1 := zElt_mul_zElt v w hwv
  have hzf : zElt v w * fIdem v w = v * fIdem v w := zElt_mul_fIdem v w hwv
  have hval : involutionDiag (zElt v w) * upperRoot (fIdem v w * r) *
      (involutionDiag (zElt v w))⁻¹
      = upperRoot (v * (fIdem v w * r * zElt v w)) := by
    rw [involutionDiag_conj_upperRoot _ hz]
    congr 1
    calc zElt v w * (fIdem v w * r) * zElt v w
        = zElt v w * fIdem v w * (r * zElt v w) := by noncomm_ring
      _ = v * fIdem v w * (r * zElt v w) := by rw [hzf]
      _ = v * (fIdem v w * r * zElt v w) := by noncomm_ring
  exact ⟨hval,
    (manuscriptSentence_rankTwoUpperRootInClosure v a b hbv hba
      (fIdem v w * r * zElt v w)).2⟩

/-- **`lem:rank-two`, the printed statement.**

`RankDescentPrinted.manuscriptRankTwoNormalGeneration`. -/
theorem manuscriptSentence_rankTwoStatement : PrintedRankTwoNormalGeneration :=
  manuscriptRankTwoNormalGeneration

/-! ## Lemma `lem:ring-compression-cell`, the proof -/

section CompressionCell

variable {R : Type} [Ring R] (P : OneSidedInverse R)

/-- **`lem:ring-compression-cell`, proof sentence 1.**

> Here `e² = e` and `es = te = 0`.

`OneSidedInverse.e_mul_e`, `e_mul_s`, `t_mul_e`. -/
theorem manuscriptSentence_compressionCellIdempotent :
    P.e * P.e = P.e ∧ P.e * P.s = 0 ∧ P.t * P.e = 0 :=
  ⟨P.e_mul_e, P.e_mul_s, P.t_mul_e⟩

/-- **`lem:ring-compression-cell`, proof sentence 2.**

> For `i = 1,2,3`, set `uᵢ = e_{4i}(t-1) e_{i4}(1) e_{4i}(s-1) e_{i4}(-t)`.

Definitional: `OneSidedCompressor.compressorPiece`. -/
theorem manuscriptSentence_compressionCellPieceDef (i : Fin 3) :
    compressorPiece P i
      = elementaryRoot lastIdx (coreIdx i) (last_ne_coreIdx i) (P.t - 1) *
          elementaryRoot (coreIdx i) lastIdx (coreIdx_ne_last i) 1 *
            elementaryRoot lastIdx (coreIdx i) (last_ne_coreIdx i) (P.s - 1) *
              elementaryRoot (coreIdx i) lastIdx (coreIdx_ne_last i) (-P.t) :=
  rfl

/-- **`lem:ring-compression-cell`, proof sentence 3.**

> Its block on coordinates `(i,4)` is `(s e; 0 t)`.

`OneSidedCompressor.compressorPiece_val`. -/
theorem manuscriptSentence_compressionCellPieceBlock (i : Fin 3) :
    (↑(↑(compressorPiece P i) : (Matrix (Fin 4) (Fin 4) R)ˣ) :
        Matrix (Fin 4) (Fin 4) R) = compressorPieceMatrix P i :=
  compressorPiece_val P i

/-- **`lem:ring-compression-cell`, proof sentences 4-5.**

> so `u = u₃u₂u₁ ∈ EL₄(R)` is the matrix `(s 0 0 e; 0 s 0 et; 0 0 s et²;
> 0 0 0 t³)`, invertible as a product of elementary matrices.

Membership in `EL₄(R)` is the type of `compressor`; the displayed matrix is
`compressor_val`; invertibility as a two-sided inverse pair of matrices is
`compressorMatrix_mul_inv` and `compressorInvMatrix_mul`. -/
theorem manuscriptSentence_compressionCellMatrixAndInvertible :
    (↑(↑(compressor P) : (Matrix (Fin 4) (Fin 4) R)ˣ) :
        Matrix (Fin 4) (Fin 4) R) = compressorMatrix P ∧
      compressorMatrix P * compressorInvMatrix P = 1 ∧
      compressorInvMatrix P * compressorMatrix P = 1 :=
  ⟨compressor_val P, compressorMatrix_mul_inv P, compressorInvMatrix_mul P⟩

/-- **`lem:ring-compression-cell`, proof sentence 6, `eq:intertwine`.**

> For `1 ≤ i ≠ j ≤ 3` and `a ∈ R`, `u e_{ij}(a) = e_{ij}(sat) u`.

`OneSidedCompressor.compressor_mul_coreRoot`. -/
theorem manuscriptSentence_compressionCellIntertwine (i j : Fin 3) (hij : i ≠ j)
    (a : R) :
    compressor P * elementaryRoot (coreIdx i) (coreIdx j) (coreIdx_injective.ne hij) a
      = elementaryRoot (coreIdx i) (coreIdx j) (coreIdx_injective.ne hij)
          (P.s * a * P.t) * compressor P :=
  compressor_mul_coreRoot P i j hij a

/-- **`lem:ring-compression-cell`, proof sentences 7-9.**

> both sides differ from `u` by one entry, `sa` in position `(i,j)`, since
> on the right the increment `sat·(s,…,et^{j-1})` from row `j` of `u`
> contributes `sa·ts = sa` in position `(i,j)` and `sa·te·t^{j-1} = 0` in
> position `(i,4)`.  So `uLu⁻¹ ≤ L`, and `eq:intertwine` gives the last
> assertion.

The entry computation is
`FullDefectRingSentences.manuscriptSentence_intertwineEntries`, already
landed and proved at this exact generality (an arbitrary one-sided pair over
an arbitrary ring, not the printed lemma's own `R`).  `uLu⁻¹ ≤ L` is
`compressor_compresses_core`.  The off-diagonal form of every entry of a
matrix in `uLu⁻¹` -- the printed lemma's own closing sentence, with no badge
in the manuscript until this module's sibling
`RankFourCompressionCellPrinted` -- is
`compressor_conj_core_offDiag_sandwich`. -/
theorem manuscriptSentence_compressionCellCoreAndOffDiag (a : R) :
    (P.s * a * P.t * P.s = P.s * a ∧ ∀ x : R, P.s * a * P.t * (P.e * x) = 0) ∧
      (∀ g ∈ core R, compressor P * g * (compressor P)⁻¹ ∈ core R) ∧
      (∀ g ∈ core R, ∀ i j : Fin 4, i ≠ j →
        ∃ b : R,
          (↑(↑(compressor P * g * (compressor P)⁻¹) :
                (Matrix (Fin 4) (Fin 4) R)ˣ) : Matrix (Fin 4) (Fin 4) R) i j
            = P.s * b * P.t) :=
  ⟨manuscriptSentence_intertwineEntries P a, compressor_compresses_core P,
    fun _g hg i j hij ↦ compressor_conj_core_offDiag_sandwich P hg i j hij⟩

/-- **`lem:ring-compression-cell`, proof sentence 10.**

> The element `c = [e₄₁(e), e₁₄(t)] = diag(1,1,1,1+et)` is computed in the
> block on coordinates `(1,4)` using `te = 0`.

`OneSidedCompressor.centralMark_eq_commutator` and `centralMark_val`. -/
theorem manuscriptSentence_compressionCellCentralMark :
    centralMark P =
        ⁅elementaryRoot lastIdx (coreIdx 0) (last_ne_coreIdx 0) P.e,
          elementaryRoot (coreIdx 0) lastIdx (coreIdx_ne_last 0) P.t⁆ ∧
      (↑(↑(centralMark P) : (Matrix (Fin 4) (Fin 4) R)ˣ) :
          Matrix (Fin 4) (Fin 4) R)
        = centralMarkMatrix P :=
  ⟨centralMark_eq_commutator P, centralMark_val P⟩

/-- **`lem:ring-compression-cell`, proof sentence 11.**

> and a diagonal matrix of this shape commutes with every `diag(A,1)`, so
> `c ∈ C_G(L)`.

`OneSidedCompressor.centralMark_commute_coreRoot` and
`centralMark_commute_core`. -/
theorem manuscriptSentence_compressionCellCentralMarkCentral :
    (∀ (i j : Fin 3) (hij : i ≠ j) (a : R),
        Commute (centralMark P)
          (elementaryRoot (coreIdx i) (coreIdx j) (coreIdx_injective.ne hij) a)) ∧
      ∀ g ∈ core R, Commute (centralMark P) g :=
  ⟨centralMark_commute_coreRoot P, centralMark_commute_core P⟩

/-- **`lem:ring-compression-cell`, proof sentences 12-13.**

> Both `uc` and `e₁₂(e)u` equal `u + et E₁₄` ... So `ucu⁻¹ = e₁₂(e)`.

`OneSidedCompressor.compressor_mul_centralMark` is the printed equality of
the two products (the intermediate form `u + et E₁₄` is folded into the same
matrix computation and is not separately named); `compressor_conj_centralMark`
is the displayed conclusion. -/
theorem manuscriptSentence_compressionCellConjCentralMark :
    compressor P * centralMark P =
        elementaryRoot (coreIdx 0) (coreIdx 1) (coreIdx_injective.ne zeroNeOne)
          P.e * compressor P ∧
      compressor P * centralMark P * (compressor P)⁻¹ =
        elementaryRoot (coreIdx 0) (coreIdx 1) (coreIdx_injective.ne zeroNeOne)
          P.e :=
  ⟨compressor_mul_centralMark P, compressor_conj_centralMark P⟩

/-- **`lem:ring-compression-cell`, proof sentence 14.**

> and the Steinberg relation `[e₁₂(e), e₂₃(1)] = e₁₃(e)` gives the second
> identity.

`OneSidedCompressor.defect_eq`. -/
theorem manuscriptSentence_compressionCellDefect :
    ⁅compressor P * centralMark P * (compressor P)⁻¹, printedEll R⁆
      = printedDefectRoot P :=
  defect_eq P

end CompressionCell

/-- **`lem:ring-compression-cell`, the printed statement, with the
off-diagonal clause included and proved.**

`RankFourCompressionCellPrinted.manuscriptRankFourCompressionCell`. -/
theorem manuscriptSentence_compressionCellStatement :
    PrintedRankFourCompressionCell :=
  manuscriptRankFourCompressionCell

/-! ## Corollary `cor:simple-infinite-ring`, the proof -/

section SimpleInfiniteRing

open GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRing

/-- **`cor:simple-infinite-ring`, proof sentence 1 (the simple case).**

> In the first case choose `ts = 1 ≠ st`; then `1 - st` is a nonzero
> idempotent, and since `R` is simple it generates `R` as a two-sided ideal.

`exists_oneSidedInverse_of_not_isDedekindFinite` produces the pair from "not
directly finite"; `isSimpleRing_full_of_not_directlyFinite` is the printed
fullness verification. -/
theorem manuscriptSentence_simpleRingChooseAndFull {R : Type} [Ring R]
    [IsSimpleRing R] (hdf : ¬ IsDedekindFiniteMonoid R) :
    ∃ s t : R, t * s = 1 ∧ s * t ≠ 1 ∧
      ∃ (m : ℕ) (a b : Fin m → R), ∑ k, a k * (1 - s * t) * b k = 1 := by
  obtain ⟨s, t, hts, hst⟩ := exists_oneSidedInverse_of_not_isDedekindFinite hdf
  obtain ⟨_, hfull⟩ := isSimpleRing_full_of_not_directlyFinite hts hst
  exact ⟨s, t, hts, hst, hfull⟩

/-- **`cor:simple-infinite-ring`, proof sentence 2 (the Leavitt case).**

> In the second case, with generators `s₁,…,s_m,t₁,…,t_m` subject to
> `tᵢsⱼ = δᵢⱼ` and `∑ᵢsᵢtᵢ = 1`, take `s = s₁` and `t = t₁`; then
> `1 - s₁t₁ = ∑_{i≥2}sᵢtᵢ` and `t₂(1-s₁t₁)s₂ = 1`.

`completeMatrixFamily_full`, at the printed indices `1` and `2` (the
manuscript's own indexing; the printed intermediate identity
`1 - s₁t₁ = ∑_{i≥2}sᵢtᵢ` is not needed, since the single sandwich is checked
directly from the two orthogonality relations `tᵢsⱼ = δᵢⱼ`). -/
theorem manuscriptSentence_leavittChooseAndFull {A : Type*} [Ring A]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (F : CompleteMatrixFamily A ι)
    {i j : ι} (hij : i ≠ j) :
    F.right i * F.left i = 1 ∧
      ∃ (m : ℕ) (a b : Fin m → A),
        ∑ k, a k * (1 - F.left i * F.right i) * b k = 1 :=
  completeMatrixFamily_full F hij

open GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingEJZUnconditional in
/-- **`cor:simple-infinite-ring`, proof sentence 3.**

> Theorem `thm:full-defect-ring` applies in both cases.

`manuscriptSimpleInfiniteRingAllCharacteristics` and
`manuscriptLeavittAlgebraFullDefectAllCharacteristics`, already landed
closed (the Ershov--Jaikin-Zapirain hypothesis discharged by
`IntegralColumnPlaneClosure.finitelyGeneratedRingGeneralRankElementaryPropertyT`),
apply `thm:full-defect-ring` to exactly the pairs produced by the two
preceding sentences. -/
theorem manuscriptSentence_simpleInfiniteRingCorollaryStatement :
    PrintedSimpleInfiniteRing ∧ PrintedLeavittAlgebraFullDefect :=
  ⟨manuscriptSimpleInfiniteRingAllCharacteristics,
    manuscriptLeavittAlgebraFullDefectAllCharacteristics⟩

end SimpleInfiniteRing

/-! ## Corollary `cor:one-sided-ring-maximal`, the proof -/

section OneSidedRingMaximal

open GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRing
open GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingEJZUnconditional

/-- **`cor:one-sided-ring-maximal`, proof sentence 1.**

> Choose `s, t ∈ R` with `ts = 1 ≠ st`, and let `S` be the unital subring
> they generate.

The choice of `s, t` is `exists_oneSidedInverse_of_not_isDedekindFinite`; the
subring `S` is `Subring.closure {s, t}`, exactly as
`manuscriptOneSidedCompressorStrictContainment` builds it. -/
theorem manuscriptSentence_oneSidedMaximalChooseSubring {R : Type} [Ring R]
    (hdf : ¬ IsDedekindFiniteMonoid R) :
    ∃ s t : R, t * s = 1 ∧ s * t ≠ 1 ∧
      s ∈ Subring.closure ({s, t} : Set R) ∧
        t ∈ Subring.closure ({s, t} : Set R) := by
  obtain ⟨s, t, hts, hst⟩ := exists_oneSidedInverse_of_not_isDedekindFinite hdf
  exact ⟨s, t, hts, hst, Subring.subset_closure (by simp),
    Subring.subset_closure (by simp)⟩

/-- **`cor:one-sided-ring-maximal`, proof sentences 2-3.**

> Let `u` and `L = EL₃(S)` be as in Lemma `lem:ring-compression-cell` for
> `S`; then `L` has property `(T)`, and the compression is strict, since
> `e(sat) = 0` while `e·1 = e ≠ 0` puts `e₁₂(1)` in `L \ uLu⁻¹`.

Property `(T)` of `L = EL₃(S)` is not re-proved here: it is exactly
`HeadlineCitationSentences.manuscriptSentence_pairSubringElementaryPropertyT`
(landed), which carries the printed clause "`S` is the subring `s, t`
generate; `L` has property `(T)`" as a closed statement about
`Subring.closure {s, t}`.  This carrier is the strict-compression half only,
with `L` taken as the image of `EL₃(S)` in `EL_n(R)`: `compressorOf_strict`,
closed with no property-`(T)` input at all (only `e ≠ 0`). -/
theorem manuscriptSentence_oneSidedMaximalStrictCompression
    {R : Type} [Ring R] {n : ℕ} (P : OneSidedInverse R) (hn : 4 ≤ n)
    (S : Subring R) (hs : P.s ∈ S) (ht : P.t ∈ S) (he : P.e ≠ 0) :
    ((coreOverHom S hn).range).map
        (MulAut.conj (compressorOf P hn)).toMonoidHom <
      (coreOverHom S hn).range :=
  compressorOf_strict P hn S hs ht he

/-- **`cor:one-sided-ring-maximal`, proof sentence 4.**

> By Proposition `prop:max-infinite` applied to `L ≤ EL_n(R)` and `u`,
> `C*_max(EL_n(R))` contains a proper isometry.

`properIsometry_of_strictCompression`, taking the property-`(T)` subgroup and
the strict compression of the two preceding sentences as its input. -/
theorem manuscriptSentence_oneSidedMaximalProperIsometry {G : Type} [Group G]
    (Γ : Subgroup G) (u : G) (hT : HasKazhdanPropertyT.{0, 0} ↥Γ)
    (hlt : Γ.map (MulAut.conj u).toMonoidHom < Γ) :
    ∃ v : MaximalGroupCStar G, star v * v = 1 ∧ ¬ IsUnit v :=
  (properIsometry_of_strictCompression Γ u hT hlt).1

/-- **`cor:one-sided-ring-maximal`, proof sentence 5.**

> If `R ≠ 0` satisfies the hypothesis of `thm:full-defect-ring`, then
> `G = EL_n(R)` is countable and nontrivial, and by `thm:full-defect-ring`
> it is not MF.  The algebra `C*_r(G)` is separable, stably finite because
> its canonical trace is faithful, and not MF by
> Lemma `prop:mf-residual-calculus`.

`FullDefectRingEJZUnconditional.manuscriptOneSidedRingMaximalReducedCStarAllCharacteristics`,
already landed closed (the Ershov--Jaikin-Zapirain hypothesis discharged by
`IntegralColumnPlaneClosure.finitelyGeneratedRingGeneralRankElementaryPropertyT`),
proves exactly this printed conclusion (separable, stably finite, not MF
for the reduced group `C^*`-algebra). -/
theorem manuscriptSentence_oneSidedMaximalReducedCStar :
    PrintedOneSidedRingMaximalReducedCStar :=
  manuscriptOneSidedRingMaximalReducedCStarAllCharacteristics

/-- **`cor:one-sided-ring-maximal`, proof sentence 6.**

> Finally, the map `ȷ` from the proof of `thm:full-defect-ring` is
> injective, since `Tᵢȷ(A)Sⱼ = Aᵢⱼ`, and sends `EL₄(R)` into `R^×`; that
> group is not MF, and MF passes to subgroups.  So `R^×` is not MF.

The reproducing identity is `RankDescent.wordT_mul_jMap_mul_wordS`, and
injectivity from it is `RankDescent.jMap_injective`; the printed corollary
`R^× is not MF` is `manuscriptUnitGroupNotMFFromEJZ`, already landed. -/
theorem manuscriptSentence_oneSidedMaximalJInjective {R : Type*} [Ring R]
    (S T : Fin 4 → R) (hTS : ∀ i j, T i * S j = if i = j then 1 else 0) :
    (∀ i j A, T i * jMap S T A * S j = A i j) ∧
      Function.Injective (jMap S T) :=
  ⟨fun i j A ↦ wordT_mul_jMap_mul_wordS S T hTS i j A, jMap_injective S T hTS⟩

end OneSidedRingMaximal

open GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRankTwo in
open GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingEJZUnconditional in
/-- **`cor:one-sided-ring-maximal`, proof sentence 6, the conclusion.**

> that group is not MF, and MF passes to subgroups.  So `R^×` is not MF.

`FullDefectRingEJZUnconditional.manuscriptUnitGroupNotMFAllCharacteristics`,
already landed closed (the Ershov--Jaikin-Zapirain hypothesis discharged by
`IntegralColumnPlaneClosure.finitelyGeneratedRingGeneralRankElementaryPropertyT`). -/
theorem manuscriptSentence_oneSidedMaximalUnitGroupNotMF :
    PrintedUnitGroupNotMF :=
  manuscriptUnitGroupNotMFAllCharacteristics

end OneSidedSentences
end NonMFSentences
end Manuscript
end GroupApproximation

open GroupApproximation
open GroupApproximation.Manuscript.NonMFSentences.OneSidedSentences

#audit_axioms manuscriptSentence_twoCopiesSetup
#audit_axioms manuscriptSentence_twoCopiesDefine
#audit_axioms manuscriptSentence_twoCopiesFourEquations
#audit_axioms manuscriptSentence_twoCopiesOrthogonality
#audit_axioms manuscriptSentence_twoCopiesConverse
#audit_axioms commutator_mem_normalClosure_self
#audit_axioms manuscriptSentence_rankTwoGeneratorValueAndClosure
#audit_axioms manuscriptSentence_rankTwoUpperRootInClosure
#audit_axioms manuscriptSentence_rankTwoInvolutionSetup
#audit_axioms manuscriptSentence_rankTwoInvolutionSquareAndFix
#audit_axioms manuscriptSentence_rankTwoInvolutionDiag
#audit_axioms manuscriptSentence_rankTwoConjugateInClosure
#audit_axioms manuscriptSentence_rankTwoStatement
#audit_axioms manuscriptSentence_compressionCellIdempotent
#audit_axioms manuscriptSentence_compressionCellPieceDef
#audit_axioms manuscriptSentence_compressionCellPieceBlock
#audit_axioms manuscriptSentence_compressionCellMatrixAndInvertible
#audit_axioms manuscriptSentence_compressionCellIntertwine
#audit_axioms manuscriptSentence_compressionCellCoreAndOffDiag
#audit_axioms manuscriptSentence_compressionCellCentralMark
#audit_axioms manuscriptSentence_compressionCellCentralMarkCentral
#audit_axioms manuscriptSentence_compressionCellConjCentralMark
#audit_axioms manuscriptSentence_compressionCellDefect
#audit_axioms manuscriptSentence_compressionCellStatement
#audit_axioms manuscriptSentence_simpleRingChooseAndFull
#audit_axioms manuscriptSentence_leavittChooseAndFull
#audit_axioms manuscriptSentence_simpleInfiniteRingCorollaryStatement
#audit_axioms manuscriptSentence_oneSidedMaximalChooseSubring
#audit_axioms manuscriptSentence_oneSidedMaximalStrictCompression
#audit_axioms manuscriptSentence_oneSidedMaximalProperIsometry
#audit_axioms manuscriptSentence_oneSidedMaximalReducedCStar
#audit_axioms manuscriptSentence_oneSidedMaximalJInjective
#audit_axioms manuscriptSentence_oneSidedMaximalUnitGroupNotMF
