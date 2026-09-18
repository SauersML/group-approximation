import GroupApproximation.Manuscript.NonMFNotes.Full.LiteralDecidable.Forward
import Mathlib.Analysis.Matrix.Order

/-!
# The literal predicate gives solutions of the polynomial system (lane NN02c)

Manuscript: `thm:mf-radical-arithmetic` (non_mf_group_notes.tex), sentence
"This is decidable over the real closed field" (Tarski 1951, Seidenberg 1954).

Given generator unitaries `U` witnessing `NN02b.LiteralD c v n d`, we fill in every block of
the system `encodeC ((c, v), n, d)`:

* block `(0, i)` is `U i`, block `(1, encode u)` is the value `u(U)`;
* block `(2, encode r)` is `M = 2^(n+10) (W_r - 1)`, which has `‖M‖ ≤ 1`, so `1 - Mᴴ M` is
  positive semidefinite and equals `Bᴴ B` for some `B`, stored in block `(3, encode r)`
  (`exists_gram_complement`);
* block `(4, 0)` holds a unit vector `x` at which `W_v - 1` reaches its norm
  (`exists_unit_vector_attaining_l2_opNorm`), and block `(5, 0)` holds `(W_v - 1) x`.

With `Forward` this gives `PolySystem.Holds (literalSystem z) ↔ LiteralD` (`literalSystem_holds_iff`).
-/

namespace GroupApproximation.Full.NN02c

open Matrix

noncomputable section

/-! ### Assignments built from blocks -/

/-- Entry `(j, k)` of a `d × d` matrix, `0` outside the range. -/
def ent {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (j k : ℕ) : ℂ :=
  if h : j < d ∧ k < d then A ⟨j, h.1⟩ ⟨k, h.2⟩ else 0

theorem ent_fin {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (j k : Fin d) : ent A j k = A j k :=
  dif_pos (show (j : ℕ) < d ∧ (k : ℕ) < d from ⟨j.2, k.2⟩)

/-- The assignment whose block `(b, e)` is `G b e`. -/
def blockAssign {d : ℕ} (G : ℕ → ℕ → Matrix (Fin d) (Fin d) ℂ) (m : ℕ) : ℂ :=
  ent (G m.unpair.1 m.unpair.2.unpair.1) m.unpair.2.unpair.2.unpair.1
    m.unpair.2.unpair.2.unpair.2

theorem blockAssign_cv {d : ℕ} (G : ℕ → ℕ → Matrix (Fin d) (Fin d) ℂ) (b e j k : ℕ) :
    blockAssign G (cv b e j k) = ent (G b e) j k := by
  simp only [blockAssign, cv, Nat.unpair_pair]

theorem blk_blockAssign {d : ℕ} (G : ℕ → ℕ → Matrix (Fin d) (Fin d) ℂ) (b e : ℕ) :
    blk (blockAssign G) d b e = G b e := by
  ext j k
  rw [blk_apply, blockAssign_cv, ent_fin]

theorem colVec_blockAssign {d : ℕ} (G : ℕ → ℕ → Matrix (Fin d) (Fin d) ℂ) (b : ℕ)
    (x : Fin d → ℂ) (hG : G b 0 = Matrix.of fun j (_ : Fin d) => x j) :
    colVec (blockAssign G) d b = x := by
  funext j
  show blockAssign G (cv b 0 j 0) = x j
  rw [blockAssign_cv, hG]
  exact dif_pos (show (j : ℕ) < d ∧ 0 < d from ⟨j.2, lt_of_le_of_lt (Nat.zero_le _) j.2⟩)

/-- Decoding a word code (the empty word on invalid codes). -/
def decodeWord (e : ℕ) : List (ℕ × Bool) :=
  (Encodable.decode e : Option (List (ℕ × Bool))).getD []

theorem decodeWord_encode (u : List (ℕ × Bool)) : decodeWord (Encodable.encode u) = u := by
  rw [decodeWord, Encodable.encodek, Option.getD_some]

/-! ### Contractions have Gram complements -/

section Gram

open scoped MatrixOrder ComplexOrder

/-- If `M` does not increase `ℓ²` norms, then `1 = Mᴴ M + Bᴴ B` for some `B`. -/
theorem exists_gram_complement {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ)
    (hM : ∀ x : Fin d → ℂ,
      ∑ i, Complex.normSq ((M *ᵥ x) i) ≤ ∑ i, Complex.normSq (x i)) :
    ∃ B : Matrix (Fin d) (Fin d) ℂ, 1 = Mᴴ * M + Bᴴ * B := by
  have hpsd : (1 - Mᴴ * M).PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
    · show (1 - Mᴴ * M)ᴴ = 1 - Mᴴ * M
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose]
    · rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, star_dotProduct_self_eq x,
        star_dotProduct_gram M x, ← Complex.ofReal_sub]
      exact Complex.zero_le_real.mpr (sub_nonneg.mpr (hM x))
  obtain ⟨G, hG⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hpsd.nonneg
  have hG' : 1 - Mᴴ * M = Gᴴ * G := hG
  refine ⟨G, ?_⟩
  rw [← hG']
  exact (add_sub_cancel (Mᴴ * M) 1).symm

end Gram

open scoped Matrix.Norms.L2Operator

theorem exists_gram_complement_of_norm_le_one {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ)
    (hM : ‖M‖ ≤ 1) : ∃ B : Matrix (Fin d) (Fin d) ℂ, 1 = Mᴴ * M + Bᴴ * B := by
  refine exists_gram_complement M fun x => ?_
  have h1 : ‖M‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg M) hM
  have h0 : 0 ≤ ∑ i, Complex.normSq (x i) :=
    Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  calc ∑ i, Complex.normSq ((M *ᵥ x) i) ≤ ‖M‖ ^ 2 * ∑ i, Complex.normSq (x i) :=
        GroupApproximation.KazhdanCornerMatrices.sum_normSq_mulVec_le_general M x
    _ ≤ 1 * ∑ i, Complex.normSq (x i) := mul_le_mul_of_nonneg_right h1 h0
    _ = ∑ i, Complex.normSq (x i) := one_mul _

/-- `‖W - 1‖ ≤ 2^(-n-10)` gives `‖2^(n+10) (W - 1)‖ ≤ 1`. -/
theorem norm_smul_sub_one_le_one {d : ℕ} (n : ℕ) (W : Matrix (Fin d) (Fin d) ℂ)
    (hW : ‖W - 1‖ ≤ NN02b.literalDefectBound n) : ‖((scale n : ℕ) : ℂ) • (W - 1)‖ ≤ 1 := by
  have h2 : ((2 ^ (n + 10) : ℕ) : ℝ) = (2 : ℝ) ^ (n + 10) := by norm_num
  have hS : ‖((scale n : ℕ) : ℂ)‖ * NN02b.literalDefectBound n = 1 := by
    rw [Complex.norm_natCast, scale_eq, NN02b.literalDefectBound_eq, h2]
    exact mul_inv_cancel₀ (pow_ne_zero _ two_ne_zero)
  calc ‖((scale n : ℕ) : ℂ) • (W - 1)‖ ≤ ‖((scale n : ℕ) : ℂ)‖ * ‖W - 1‖ := norm_smul_le _ _
    _ ≤ ‖((scale n : ℕ) : ℂ)‖ * NN02b.literalDefectBound n :=
      mul_le_mul_of_nonneg_left hW (norm_nonneg _)
    _ = 1 := hS

/-- A matrix of norm at least `1/2` has a unit vector `x` with `0 ≤ re (4 ⟪X x, X x⟫ - 1)`. -/
theorem unit_vector_of_half_le {d : ℕ} (hd : 0 < d) (X : Matrix (Fin d) (Fin d) ℂ)
    (hX : 1 / 2 ≤ ‖X‖) :
    ∃ x : Fin d → ℂ, star x ⬝ᵥ x = 1 ∧
      0 ≤ (((4 : ℕ) : ℂ) * (star (X *ᵥ x) ⬝ᵥ (X *ᵥ x)) - 1).re := by
  obtain ⟨x, hx1, hx2⟩ :=
    GroupApproximation.Manuscript.MFRecognition.Certificates.exists_unit_vector_attaining_l2_opNorm
      (⟨⟨0, hd⟩⟩ : Nonempty (Fin d)) X
  refine ⟨x, ?_, ?_⟩
  · rw [star_dotProduct_self_eq, hx1, Complex.ofReal_one]
  · rw [star_dotProduct_self_eq, Complex.sub_re, Complex.one_re, ← Complex.ofReal_natCast,
      ← Complex.ofReal_mul, Complex.ofReal_re]
    have h4 : ((1 : ℝ) / 2) ^ 2 ≤ ‖X‖ ^ 2 := pow_le_pow_left₀ (by norm_num) hX 2
    have h5 : ((1 : ℝ) / 2) ^ 2 = 1 / 4 := by norm_num
    have h44 : ((4 : ℕ) : ℝ) = 4 := by norm_num
    rw [h5] at h4
    rw [h44]
    linarith

/-! ### The blocks of a solution -/

/-- The matrix value of a coded word at `U`. -/
def wv (c : PresentationCodes.PresentationCode) {d : ℕ}
    (U : Fin (PresentationCodes.genCount c) → Matrix.unitaryGroup (Fin d) ℂ)
    (u : List (ℕ × Bool)) : Matrix (Fin d) (Fin d) ℂ :=
  ((NN02b.literalWordValue c U u : Matrix.unitaryGroup (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ)

open Classical in
/-- A matrix `B` with `1 = Mᴴ M + Bᴴ B`, when there is one. -/
def sqBlock {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  if h : ∃ B : Matrix (Fin d) (Fin d) ℂ, 1 = Mᴴ * M + Bᴴ * B then h.choose else 0

open Classical in
theorem sqBlock_spec {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ)
    (h : ∃ B : Matrix (Fin d) (Fin d) ℂ, 1 = Mᴴ * M + Bᴴ * B) :
    1 = Mᴴ * M + (sqBlock M)ᴴ * sqBlock M := by
  rw [sqBlock, dif_pos h]
  exact h.choose_spec

/-- The blocks of the solution attached to `U`, a vector `x` and `y = (W_v - 1) x`. -/
def solBlocks (c : PresentationCodes.PresentationCode) {d : ℕ} (n : ℕ)
    (U : Fin (PresentationCodes.genCount c) → Matrix.unitaryGroup (Fin d) ℂ)
    (x y : Fin d → ℂ) : ℕ → ℕ → Matrix (Fin d) (Fin d) ℂ
  | 0, e => if h : e < c.1 + 1 then (U ⟨e, h⟩ : Matrix (Fin d) (Fin d) ℂ) else 0
  | 1, e => wv c U (decodeWord e)
  | 2, e => ((scale n : ℕ) : ℂ) • (wv c U (decodeWord e) - 1)
  | 3, e => sqBlock (((scale n : ℕ) : ℂ) • (wv c U (decodeWord e) - 1))
  | 4, _ => Matrix.of fun j _ => x j
  | 5, _ => Matrix.of fun j _ => y j
  | _, _ => 0

section Blocks

variable (c : PresentationCodes.PresentationCode) {d : ℕ} (n : ℕ)
  (U : Fin (PresentationCodes.genCount c) → Matrix.unitaryGroup (Fin d) ℂ) (x y : Fin d → ℂ)

theorem sol0 {i : ℕ} (hi : i < c.1 + 1) :
    solBlocks c n U x y 0 i = (U ⟨i, hi⟩ : Matrix (Fin d) (Fin d) ℂ) :=
  dif_pos hi

theorem sol1 (u : List (ℕ × Bool)) : solBlocks c n U x y 1 (Encodable.encode u) = wv c U u := by
  show wv c U (decodeWord (Encodable.encode u)) = wv c U u
  rw [decodeWord_encode]

theorem sol2 (e : ℕ) :
    solBlocks c n U x y 2 e = ((scale n : ℕ) : ℂ) • (solBlocks c n U x y 1 e - 1) :=
  rfl

theorem sol3 (e : ℕ) : solBlocks c n U x y 3 e = sqBlock (solBlocks c n U x y 2 e) :=
  rfl

theorem colVec_sol4 : colVec (blockAssign (solBlocks c n U x y)) d 4 = x :=
  colVec_blockAssign (solBlocks c n U x y) 4 x rfl

theorem colVec_sol5 : colVec (blockAssign (solBlocks c n U x y)) d 5 = y :=
  colVec_blockAssign (solBlocks c n U x y) 5 y rfl

theorem letterMat_sol (a : ℕ × Bool) :
    letterMat (blockAssign (solBlocks c n U x y)) (c.1 + 1) d a =
      bif a.2 then (U (PresentationCodes.letterOf c a.1) : Matrix (Fin d) (Fin d) ℂ)
        else (U (PresentationCodes.letterOf c a.1) : Matrix (Fin d) (Fin d) ℂ)ᴴ := by
  have h0 : blk (blockAssign (solBlocks c n U x y)) d 0 (a.1 % (c.1 + 1)) =
      (U (PresentationCodes.letterOf c a.1) : Matrix (Fin d) (Fin d) ℂ) := by
    rw [blk_blockAssign]
    exact dif_pos (show a.1 % (c.1 + 1) < c.1 + 1 from Nat.mod_lt a.1 (Nat.succ_pos c.1))
  show (bif a.2 then blk (blockAssign (solBlocks c n U x y)) d 0 (a.1 % (c.1 + 1))
      else (blk (blockAssign (solBlocks c n U x y)) d 0 (a.1 % (c.1 + 1)))ᴴ) = _
  rw [h0]

/-- The word blocks satisfy the word recursion. -/
theorem wordCond_sol (u : List (ℕ × Bool)) :
    WordCond (blockAssign (solBlocks c n U x y)) (c.1 + 1) d u := by
  induction u with
  | nil =>
    show blk (blockAssign (solBlocks c n U x y)) d 1
      (Encodable.encode ([] : List (ℕ × Bool))) = 1
    rw [blk_blockAssign, sol1 c n U x y []]
    exact coe_literalWordValue_nil c U
  | cons a u ih =>
    refine ⟨?_, ih⟩
    rw [blk_blockAssign, blk_blockAssign, sol1 c n U x y (a :: u), sol1 c n U x y u,
      letterMat_sol c n U x y a]
    exact coe_literalWordValue_cons c U a u

end Blocks

/-! ### `LiteralD` gives a solution -/

/-- **`D(P,v,n,d)` gives a solution of the system** (`thm:mf-radical-arithmetic`). -/
theorem solution_of_literalD (z : ((ℕ × List (List (ℕ × Bool))) × List (ℕ × Bool)) × ℕ × ℕ)
    (h : NN02b.LiteralD z.1.1 z.1.2 z.2.1 z.2.2) : ∃ ζ : ℕ → ℂ, Solution ζ z := by
  have hd : 0 < z.2.2 := NN02b.literalD_dim_pos h
  obtain ⟨U, hR, hV⟩ := h
  obtain ⟨x, hx, hnn⟩ := unit_vector_of_half_le hd (wv z.1.1 U z.1.2 - 1) hV
  refine ⟨blockAssign (solBlocks z.1.1 z.2.1 U x ((wv z.1.1 U z.1.2 - 1) *ᵥ x)),
    ⟨⟨fun i hi => ?_, fun r hr => ?_, ?_⟩, ?_⟩⟩
  · rw [blk_blockAssign, sol0 z.1.1 z.2.1 U x _ hi]
    exact Matrix.mem_unitaryGroup_iff'.mp (U ⟨i, hi⟩).2
  · have hnorm : ‖solBlocks z.1.1 z.2.1 U x ((wv z.1.1 U z.1.2 - 1) *ᵥ x) 2
        (Encodable.encode r)‖ ≤ 1 := by
      rw [sol2, sol1]
      exact norm_smul_sub_one_le_one z.2.1 (wv z.1.1 U r) (hR r hr)
    refine ⟨wordCond_sol z.1.1 z.2.1 U x _ r, ?_, ?_⟩
    · rw [blk_blockAssign, blk_blockAssign]
      exact sol2 z.1.1 z.2.1 U x _ (Encodable.encode r)
    · rw [blk_blockAssign, blk_blockAssign, sol3 z.1.1 z.2.1 U x _ (Encodable.encode r)]
      exact sqBlock_spec _ (exists_gram_complement_of_norm_le_one _ hnorm)
  · refine ⟨wordCond_sol z.1.1 z.2.1 U x _ z.1.2, ?_, ?_⟩
    · rw [colVec_sol4 z.1.1 z.2.1 U x _]
      exact hx
    · rw [colVec_sol4 z.1.1 z.2.1 U x _, colVec_sol5 z.1.1 z.2.1 U x _, blk_blockAssign,
        sol1 z.1.1 z.2.1 U x _ z.1.2]
  · rw [colVec_sol5 z.1.1 z.2.1 U x _]
    exact hnn

/-- `D(P,v,n,d)` implies solvability of the complex system. -/
theorem holds_encodeC_of_literalD
    (z : ((ℕ × List (List (ℕ × Bool))) × List (ℕ × Bool)) × ℕ × ℕ)
    (h : NN02b.LiteralD z.1.1 z.1.2 z.2.1 z.2.2) : CSystem.Holds (encodeC z) :=
  (holds_encodeC_iff z).mpr (solution_of_literalD z h)

/-- The complex system of `z` is solvable iff `D(P,v,n,d)` holds. -/
theorem holds_encodeC_iff_literalD
    (z : ((ℕ × List (List (ℕ × Bool))) × List (ℕ × Bool)) × ℕ × ℕ) :
    CSystem.Holds (encodeC z) ↔ NN02b.LiteralD z.1.1 z.1.2 z.2.1 z.2.2 :=
  ⟨literalD_of_holds_encodeC z, holds_encodeC_of_literalD z⟩

/-- **The polynomial system of `z` holds over `ℝ` iff `D(P,v,n,d)` holds**
(`thm:mf-radical-arithmetic`, "This is decidable over the real closed field"). -/
theorem literalSystem_holds_iff
    (z : ((ℕ × List (List (ℕ × Bool))) × List (ℕ × Bool)) × ℕ × ℕ) :
    PolySystem.Holds (literalSystem z) ↔ NN02b.LiteralD z.1.1 z.1.2 z.2.1 z.2.2 :=
  (holds_compileSystem (encodeC z)).trans (holds_encodeC_iff_literalD z)

end

end GroupApproximation.Full.NN02c
