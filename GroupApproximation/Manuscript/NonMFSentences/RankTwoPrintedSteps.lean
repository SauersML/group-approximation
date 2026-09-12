import GroupApproximation.Leavitt.RankTwoNormalGeneration
import GroupApproximation.Meta.AxiomGuard

/-!
# `lem:rank-two`, the printed proof sentence by sentence

`non_mf_groups_exist.tex`, Section `sec:one-sided-inverses`, the proof of
Lemma `lem:rank-two` (tex lines 829-853 at origin/main `73c867c5b`):

> The matrix `e₁₂(v)e₂₁(b)e₁₂(-v)` has rows `(1+vb, -vbv)` and `(b, 1-bv)`, so
> for `bv=0` it is `(1+vb 0; b 1)`, and multiplying by `e₂₁(-b)` gives
> `D = diag(1+vb,1)`.  Let `N` be the normal closure of `D` in `EL₂(R)`.  For
> `r ∈ R`, `[D,e₁₂(ar)] = e₁₂((1+vb)ar-ar) = e₁₂(vr)`, since `ba=1`; so
> `e₁₂(vR) ≤ N`.  Put `f = 1-vw`, an idempotent with `fv = 0 = wf`.  Since
> `r = vwr+fr`, it remains to put `e₁₂(fR)` in `N`, and the involution
> `z = vf+fw+1-f-vfw` does this by conjugation, since `zf = vf`.  Put `x = vf`,
> `y = fw`, `q = vfw`, and `c = 1-f-q`, so that `z = x+y+c`.  From `wv = 1` and
> `fv = wf = 0`: `x² = y² = 0`, `xy = q`, `yx = f`, the idempotents `f` and `q`
> are orthogonal, and `c` annihilates `x` and `y` on both sides; so
> `z² = q+f+c = 1` and `zf = xf+yf+cf = vf`.  The factorization
> `diag(z,z⁻¹) = e₁₂(z)e₂₁(-z⁻¹)e₁₂(z) e₁₂(-1)e₂₁(1)e₁₂(-1)` puts
> `h = diag(z,z)` in `EL₂(R)`, and `h e₁₂(fr) h⁻¹ = e₁₂(zfrz) = e₁₂(v frz) ∈ N`.
> So `e₁₂(r) = e₁₂(vwr) e₁₂(fr) ∈ N` for every `r ∈ R`, and conjugating by
> `e₁₂(1)e₂₁(-1)e₁₂(1)` gives `e₂₁(R) ≤ N`.

The statement of the lemma is `RankDescentPrinted.manuscriptRankTwoNormalGeneration`
and its proof is `RankDescent.normalClosure_gen_eq_top`, which runs exactly these
steps but keeps several of them as internal `have`s.  This module states every
printed step as its own theorem, at the printed generality (an arbitrary unital
ring), along the printed route: the intermediate matrix rows, the intermediate
coefficient `(1+vb)ar - ar`, the split `r = vwr + fr`, the whole multiplication
table of `x, y, q, c`, the literal six-transvection word, and the Weyl element
`e₁₂(1)e₂₁(-1)e₁₂(1)`.  Zero-based indices: `e₁₂ = upperRoot`, `e₂₁ = lowerRoot`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMFSentences
namespace RankTwoPrintedSteps

open GroupApproximation.RankDescent
open scoped commutatorElement

variable {R : Type} [Ring R]

/-- **Printed (tex 833-834).** "Let `N` be the normal closure of `D` in `EL₂(R)`." -/
abbrev printedN (v b : R) : Subgroup (elementaryGroup (Fin 2) R) :=
  Subgroup.normalClosure ({gen v b} : Set (elementaryGroup (Fin 2) R))

theorem gen_mem_printedN (v b : R) : gen v b ∈ printedN v b :=
  Subgroup.subset_normalClosure (Set.mem_singleton _)

theorem printedN_normal (v b : R) : (printedN v b).Normal :=
  Subgroup.normalClosure_normal

/-- Every commutator of `D` with an element of `EL₂(R)` lies in `N`. -/
theorem commutator_gen_mem_printedN (v b : R) (g : elementaryGroup (Fin 2) R) :
    ⁅gen v b, g⁆ ∈ printedN v b := by
  have hD := gen_mem_printedN v b
  have hconj : g * (gen v b)⁻¹ * g⁻¹ ∈ printedN v b :=
    (printedN_normal v b).conj_mem _ ((printedN v b).inv_mem hD) g
  have heq : ⁅gen v b, g⁆ = gen v b * (g * (gen v b)⁻¹ * g⁻¹) := by
    rw [commutatorElement_def]
    group
  rw [heq]
  exact (printedN v b).mul_mem hD hconj

/-- **Printed (tex 830-833).** "The matrix `e₁₂(v)e₂₁(b)e₁₂(-v)` has rows
`(1+vb, -vbv)` and `(b, 1-bv)`" — at every `v, b`, before `bv = 0` is used. -/
theorem manuscriptSentence_rankTwoConjugateRows (v b : R) :
    (((upperRoot v * lowerRoot b * upperRoot (-v) : elementaryGroup (Fin 2) R) :
        (Matrix (Fin 2) (Fin 2) R)ˣ) : Matrix (Fin 2) (Fin 2) R)
      = !![1 + v * b, -(v * b * v); b, 1 - b * v] := by
  ext p q
  fin_cases p <;> fin_cases q <;>
    simp [upperRoot, lowerRoot, elementaryRoot, elementaryUnit,
      Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ,
      Matrix.single_apply] <;>
    noncomm_ring

/-- **Printed (tex 830-833).** "so for `bv=0` it is `(1+vb 0; b 1)`, and
multiplying by `e₂₁(-b)` gives `D = diag(1+vb,1)`", together with the printed
definition `D = [e₁₂(v), e₂₁(b)]`. -/
theorem manuscriptSentence_rankTwoGeneratorDiagonal (v b : R) (hbv : b * v = 0) :
    (((upperRoot v * lowerRoot b * upperRoot (-v) : elementaryGroup (Fin 2) R) :
        (Matrix (Fin 2) (Fin 2) R)ˣ) : Matrix (Fin 2) (Fin 2) R)
      = !![1 + v * b, 0; b, 1] ∧
    upperRoot v * lowerRoot b * upperRoot (-v) * lowerRoot (-b) = gen v b ∧
    (((gen v b : elementaryGroup (Fin 2) R) :
        (Matrix (Fin 2) (Fin 2) R)ˣ) : Matrix (Fin 2) (Fin 2) R)
      = !![1 + v * b, 0; 0, 1] := by
  refine ⟨?_, (gen_eq_word v b).symm, ?_⟩
  · rw [manuscriptSentence_rankTwoConjugateRows v b]
    have h1 : v * b * v = 0 := by rw [mul_assoc, hbv, mul_zero]
    rw [h1, neg_zero, hbv, sub_zero]
  · rw [gen_val v b hbv]
    ext p q
    fin_cases p <;> fin_cases q <;> simp [Matrix.one_apply, Matrix.single_apply]

/-- **Printed (tex 834-836).** "For `r ∈ R`, `[D,e₁₂(ar)] = e₁₂((1+vb)ar-ar) =
e₁₂(vr)`, since `ba=1`; so `e₁₂(vR) ≤ N`." -/
theorem manuscriptSentence_rankTwoCommutatorUpperRoot (v a b : R)
    (hbv : b * v = 0) (hba : b * a = 1) (r : R) :
    ⁅gen v b, upperRoot (a * r)⁆ = upperRoot ((1 + v * b) * (a * r) - a * r) ∧
      upperRoot ((1 + v * b) * (a * r) - a * r) = upperRoot (v * r) ∧
      upperRoot (v * r) ∈ printedN v b := by
  have h1 : ⁅gen v b, upperRoot (a * r)⁆
      = upperRoot ((1 + v * b) * (a * r) - a * r) := by
    rw [gen_commutator_upperRoot v b hbv (a * r)]
    congr 1
    noncomm_ring
  have h2 : upperRoot ((1 + v * b) * (a * r) - a * r) = upperRoot (v * r) := by
    congr 1
    calc (1 + v * b) * (a * r) - a * r = v * (b * a) * r := by noncomm_ring
      _ = v * r := by rw [hba, mul_one]
  refine ⟨h1, h2, ?_⟩
  rw [← h2, ← h1]
  exact commutator_gen_mem_printedN v b _

/-- **Printed (tex 836).** "Put `f = 1-vw`, an idempotent with `fv = 0 = wf`." -/
theorem manuscriptSentence_rankTwoIdempotentF (v w : R) (hwv : w * v = 1) :
    fIdem v w = 1 - v * w ∧ fIdem v w * fIdem v w = fIdem v w ∧
      fIdem v w * v = 0 ∧ w * fIdem v w = 0 :=
  ⟨rfl, f_mul_f v w hwv, f_mul_v v w hwv, w_mul_f v w hwv⟩

/-- **Printed (tex 837-841).** "Since `r = vwr+fr`, it remains to put `e₁₂(fR)`
in `N`, and the involution `z = vf+fw+1-f-vfw` does this by conjugation, since
`zf = vf`." -/
theorem manuscriptSentence_rankTwoSplitAndReduction (v w a b : R)
    (hwv : w * v = 1) (hbv : b * v = 0) (hba : b * a = 1) :
    (∀ r : R, r = v * w * r + fIdem v w * r) ∧
    ((∀ r : R, upperRoot (fIdem v w * r) ∈ printedN v b) →
      ∀ r : R, upperRoot r ∈ printedN v b) ∧
    zElt v w = v * fIdem v w + fIdem v w * w + 1 - fIdem v w - v * fIdem v w * w ∧
    zElt v w * fIdem v w = v * fIdem v w := by
  refine ⟨fun r ↦ ?_, fun hf r ↦ ?_, ?_, zElt_mul_fIdem v w hwv⟩
  · show r = v * w * r + (1 - v * w) * r
    noncomm_ring
  · have hsplit : upperRoot (v * (w * r)) * upperRoot (fIdem v w * r)
        = upperRoot r := by
      rw [upperRoot_mul]
      congr 1
      show v * (w * r) + (1 - v * w) * r = r
      noncomm_ring
    rw [← hsplit]
    exact (printedN v b).mul_mem
      (manuscriptSentence_rankTwoCommutatorUpperRoot v a b hbv hba (w * r)).2.2
      (hf r)
  · rw [zElt_eq, gIdem_eq]
    noncomm_ring

/-- **Printed (tex 841).** "Put `x = vf`, `y = fw`, `q = vfw`, and
`c = 1-f-q`, so that `z = x+y+c`." -/
theorem manuscriptSentence_rankTwoDecomposition (v w : R) :
    zElt v w = v * fIdem v w + fIdem v w * w
      + (1 - fIdem v w - v * fIdem v w * w) := by
  rw [zElt_eq, gIdem_eq]

/-- **Printed (tex 841-844).** "From `wv = 1` and `fv = wf = 0`: `x² = y² = 0`,
`xy = q`, `yx = f`, the idempotents `f` and `q` are orthogonal, and `c`
annihilates `x` and `y` on both sides; so `z² = q+f+c = 1` and
`zf = xf+yf+cf = vf`."

The whole printed multiplication table, with `x = vf`, `y = fw`, `q = vfw`,
`c = 1-f-q`, and both displayed chains of equalities. -/
theorem manuscriptSentence_rankTwoMultiplicationTable (v w : R) (hwv : w * v = 1) :
    -- x² = y² = 0
    (v * fIdem v w) * (v * fIdem v w) = 0 ∧
    (fIdem v w * w) * (fIdem v w * w) = 0 ∧
    -- xy = q, yx = f
    (v * fIdem v w) * (fIdem v w * w) = v * fIdem v w * w ∧
    (fIdem v w * w) * (v * fIdem v w) = fIdem v w ∧
    -- f and q are orthogonal idempotents
    fIdem v w * fIdem v w = fIdem v w ∧
    (v * fIdem v w * w) * (v * fIdem v w * w) = v * fIdem v w * w ∧
    fIdem v w * (v * fIdem v w * w) = 0 ∧ (v * fIdem v w * w) * fIdem v w = 0 ∧
    -- c annihilates x and y on both sides
    (1 - fIdem v w - v * fIdem v w * w) * (v * fIdem v w) = 0 ∧
    (v * fIdem v w) * (1 - fIdem v w - v * fIdem v w * w) = 0 ∧
    (1 - fIdem v w - v * fIdem v w * w) * (fIdem v w * w) = 0 ∧
    (fIdem v w * w) * (1 - fIdem v w - v * fIdem v w * w) = 0 ∧
    -- z² = q + f + c = 1
    zElt v w * zElt v w
      = v * fIdem v w * w + fIdem v w + (1 - fIdem v w - v * fIdem v w * w) ∧
    v * fIdem v w * w + fIdem v w + (1 - fIdem v w - v * fIdem v w * w) = 1 ∧
    -- zf = xf + yf + cf = vf
    zElt v w * fIdem v w
      = v * fIdem v w * fIdem v w + fIdem v w * w * fIdem v w
        + (1 - fIdem v w - v * fIdem v w * w) * fIdem v w ∧
    v * fIdem v w * fIdem v w + fIdem v w * w * fIdem v w
        + (1 - fIdem v w - v * fIdem v w * w) * fIdem v w = v * fIdem v w := by
  have hfv : fIdem v w * v = 0 := f_mul_v v w hwv
  have hwf : w * fIdem v w = 0 := w_mul_f v w hwv
  have hff : fIdem v w * fIdem v w = fIdem v w := f_mul_f v w hwv
  have hfg : fIdem v w * gIdem v w = 0 := f_mul_g v w hwv
  have hgf : gIdem v w * fIdem v w = 0 := g_mul_f v w hwv
  have hgg : gIdem v w * gIdem v w = gIdem v w := g_mul_g v w hwv
  have hwg : w * gIdem v w = fIdem v w * w := w_mul_g v w hwv
  have hgv : gIdem v w * v = v * fIdem v w := g_mul_v v w hwv
  rw [gIdem_eq] at hfg hgf hgg hwg hgv
  have hxx : (v * fIdem v w) * (v * fIdem v w) = 0 := by
    calc (v * fIdem v w) * (v * fIdem v w)
        = v * (fIdem v w * v) * fIdem v w := by noncomm_ring
      _ = 0 := by rw [hfv]; noncomm_ring
  have hyy : (fIdem v w * w) * (fIdem v w * w) = 0 := by
    calc (fIdem v w * w) * (fIdem v w * w)
        = fIdem v w * (w * fIdem v w) * w := by noncomm_ring
      _ = 0 := by rw [hwf]; noncomm_ring
  have hxy : (v * fIdem v w) * (fIdem v w * w) = v * fIdem v w * w := by
    calc (v * fIdem v w) * (fIdem v w * w)
        = v * (fIdem v w * fIdem v w) * w := by noncomm_ring
      _ = v * fIdem v w * w := by rw [hff]
  have hyx : (fIdem v w * w) * (v * fIdem v w) = fIdem v w := by
    calc (fIdem v w * w) * (v * fIdem v w)
        = fIdem v w * (w * v) * fIdem v w := by noncomm_ring
      _ = fIdem v w * fIdem v w := by rw [hwv, mul_one]
      _ = fIdem v w := hff
  have hcx : (1 - fIdem v w - v * fIdem v w * w) * (v * fIdem v w) = 0 := by
    calc (1 - fIdem v w - v * fIdem v w * w) * (v * fIdem v w)
        = v * fIdem v w - fIdem v w * v * fIdem v w
          - v * fIdem v w * w * v * fIdem v w := by noncomm_ring
      _ = v * fIdem v w - 0 * fIdem v w - v * fIdem v w * fIdem v w := by
          rw [hfv, hgv]
      _ = v * (fIdem v w - fIdem v w * fIdem v w) := by noncomm_ring
      _ = 0 := by rw [hff]; noncomm_ring
  have hxc : (v * fIdem v w) * (1 - fIdem v w - v * fIdem v w * w) = 0 := by
    calc (v * fIdem v w) * (1 - fIdem v w - v * fIdem v w * w)
        = v * fIdem v w - v * (fIdem v w * fIdem v w)
          - v * (fIdem v w * (v * fIdem v w * w)) := by noncomm_ring
      _ = 0 := by rw [hff, hfg]; noncomm_ring
  have hcy : (1 - fIdem v w - v * fIdem v w * w) * (fIdem v w * w) = 0 := by
    calc (1 - fIdem v w - v * fIdem v w * w) * (fIdem v w * w)
        = fIdem v w * w - fIdem v w * fIdem v w * w
          - v * fIdem v w * w * fIdem v w * w := by noncomm_ring
      _ = fIdem v w * w - fIdem v w * w - 0 * w := by rw [hff, hgf]
      _ = 0 := by noncomm_ring
  have hyc : (fIdem v w * w) * (1 - fIdem v w - v * fIdem v w * w) = 0 := by
    calc (fIdem v w * w) * (1 - fIdem v w - v * fIdem v w * w)
        = fIdem v w * w - fIdem v w * (w * fIdem v w)
          - fIdem v w * (w * (v * fIdem v w * w)) := by noncomm_ring
      _ = fIdem v w * w - fIdem v w * 0 - fIdem v w * (fIdem v w * w) := by
          rw [hwf, hwg]
      _ = fIdem v w * w - fIdem v w * fIdem v w * w := by noncomm_ring
      _ = 0 := by rw [hff]; noncomm_ring
  have hcc : (1 - fIdem v w - v * fIdem v w * w) * (1 - fIdem v w - v * fIdem v w * w)
      = 1 - fIdem v w - v * fIdem v w * w := by
    calc (1 - fIdem v w - v * fIdem v w * w) * (1 - fIdem v w - v * fIdem v w * w)
        = 1 - fIdem v w - v * fIdem v w * w - fIdem v w + fIdem v w * fIdem v w
          + fIdem v w * (v * fIdem v w * w) - v * fIdem v w * w
          + v * fIdem v w * w * fIdem v w
          + v * fIdem v w * w * (v * fIdem v w * w) := by noncomm_ring
      _ = 1 - fIdem v w - v * fIdem v w * w := by rw [hff, hfg, hgf, hgg]; abel
  have hz : zElt v w = v * fIdem v w + fIdem v w * w
      + (1 - fIdem v w - v * fIdem v w * w) := manuscriptSentence_rankTwoDecomposition v w
  have hzz : zElt v w * zElt v w
      = v * fIdem v w * w + fIdem v w + (1 - fIdem v w - v * fIdem v w * w) := by
    rw [hz]
    calc (v * fIdem v w + fIdem v w * w + (1 - fIdem v w - v * fIdem v w * w))
          * (v * fIdem v w + fIdem v w * w + (1 - fIdem v w - v * fIdem v w * w))
        = (v * fIdem v w) * (v * fIdem v w) + (v * fIdem v w) * (fIdem v w * w)
          + (v * fIdem v w) * (1 - fIdem v w - v * fIdem v w * w)
          + (fIdem v w * w) * (v * fIdem v w) + (fIdem v w * w) * (fIdem v w * w)
          + (fIdem v w * w) * (1 - fIdem v w - v * fIdem v w * w)
          + (1 - fIdem v w - v * fIdem v w * w) * (v * fIdem v w)
          + (1 - fIdem v w - v * fIdem v w * w) * (fIdem v w * w)
          + (1 - fIdem v w - v * fIdem v w * w)
            * (1 - fIdem v w - v * fIdem v w * w) := by noncomm_ring
      _ = v * fIdem v w * w + fIdem v w + (1 - fIdem v w - v * fIdem v w * w) := by
          rw [hxx, hxy, hxc, hyx, hyy, hyc, hcx, hcy, hcc]; abel
  have hsum : v * fIdem v w * w + fIdem v w + (1 - fIdem v w - v * fIdem v w * w)
      = 1 := by abel
  have hzf : zElt v w * fIdem v w
      = v * fIdem v w * fIdem v w + fIdem v w * w * fIdem v w
        + (1 - fIdem v w - v * fIdem v w * w) * fIdem v w := by
    rw [hz]
    noncomm_ring
  have hzf' : v * fIdem v w * fIdem v w + fIdem v w * w * fIdem v w
        + (1 - fIdem v w - v * fIdem v w * w) * fIdem v w = v * fIdem v w := by
    calc v * fIdem v w * fIdem v w + fIdem v w * w * fIdem v w
          + (1 - fIdem v w - v * fIdem v w * w) * fIdem v w
        = v * (fIdem v w * fIdem v w) + fIdem v w * (w * fIdem v w)
          + fIdem v w - fIdem v w * fIdem v w
          - v * fIdem v w * w * fIdem v w := by noncomm_ring
      _ = v * fIdem v w + fIdem v w * 0 + fIdem v w - fIdem v w - 0 := by
          rw [hff, hwf, hgf]
      _ = v * fIdem v w := by noncomm_ring
  exact ⟨hxx, hyy, hxy, hyx, hff, hgg, hfg, hgf, hcx, hxc, hcy, hyc, hzz, hsum,
    hzf, hzf'⟩

/-- **Printed (tex 844-849).** "The factorization `diag(z,z⁻¹) = e₁₂(z)e₂₁(-z⁻¹)
e₁₂(z) e₁₂(-1)e₂₁(1)e₁₂(-1)` puts `h = diag(z,z)` in `EL₂(R)`."

Since `z² = 1`, `z⁻¹ = z`; the displayed word is `involutionDiag z` literally,
and its matrix is `diag(z, z)`. -/
theorem manuscriptSentence_rankTwoSixTransvectionWord (z : R) (hz : z * z = 1) :
    involutionDiag z
      = upperRoot z * lowerRoot (-z) * upperRoot z
          * (upperRoot (-1) * lowerRoot 1 * upperRoot (-1)) ∧
    (((involutionDiag z : elementaryGroup (Fin 2) R) :
        (Matrix (Fin 2) (Fin 2) R)ˣ) : Matrix (Fin 2) (Fin 2) R)
      = !![z, 0; 0, z] := by
  refine ⟨?_, involutionDiag_val z hz⟩
  rw [involutionDiag, whiteheadThree, whiteheadThree, neg_neg]

/-- **Printed (tex 849-850).** "and `h e₁₂(fr) h⁻¹ = e₁₂(zfrz) = e₁₂(v frz) ∈ N`." -/
theorem manuscriptSentence_rankTwoConjugationIntoN (v w a b : R)
    (hwv : w * v = 1) (hbv : b * v = 0) (hba : b * a = 1) (r : R) :
    involutionDiag (zElt v w) * upperRoot (fIdem v w * r) * (involutionDiag (zElt v w))⁻¹
        = upperRoot (zElt v w * (fIdem v w * r) * zElt v w) ∧
      upperRoot (zElt v w * (fIdem v w * r) * zElt v w)
        = upperRoot (v * (fIdem v w * r * zElt v w)) ∧
      upperRoot (v * (fIdem v w * r * zElt v w)) ∈ printedN v b := by
  have hz : zElt v w * zElt v w = 1 := zElt_mul_zElt v w hwv
  have hzf : zElt v w * fIdem v w = v * fIdem v w := zElt_mul_fIdem v w hwv
  refine ⟨involutionDiag_conj_upperRoot _ hz _, ?_,
    (manuscriptSentence_rankTwoCommutatorUpperRoot v a b hbv hba _).2.2⟩
  congr 1
  calc zElt v w * (fIdem v w * r) * zElt v w
      = zElt v w * fIdem v w * (r * zElt v w) := by noncomm_ring
    _ = v * fIdem v w * (r * zElt v w) := by rw [hzf]
    _ = v * (fIdem v w * r * zElt v w) := by noncomm_ring

/-- `e₁₂(fR) ≤ N`: conjugating back by `h⁻¹`. -/
theorem upperRoot_f_mem_printedN (v w a b : R)
    (hwv : w * v = 1) (hbv : b * v = 0) (hba : b * a = 1) (r : R) :
    upperRoot (fIdem v w * r) ∈ printedN v b := by
  obtain ⟨h1, h2, h3⟩ := manuscriptSentence_rankTwoConjugationIntoN v w a b hwv hbv hba r
  have hmem : involutionDiag (zElt v w) * upperRoot (fIdem v w * r)
      * (involutionDiag (zElt v w))⁻¹ ∈ printedN v b := by
    rw [h1, h2]
    exact h3
  have hback := (printedN_normal v b).conj_mem _ hmem (involutionDiag (zElt v w))⁻¹
  have hsimp : (involutionDiag (zElt v w))⁻¹ *
      (involutionDiag (zElt v w) * upperRoot (fIdem v w * r) *
        (involutionDiag (zElt v w))⁻¹) *
      ((involutionDiag (zElt v w))⁻¹)⁻¹ = upperRoot (fIdem v w * r) := by
    group
  rwa [hsimp] at hback

/-- **Printed (tex 850-852).** "So `e₁₂(r) = e₁₂(vwr) e₁₂(fr) ∈ N` for every
`r ∈ R`, and conjugating by `e₁₂(1)e₂₁(-1)e₁₂(1)` gives `e₂₁(R) ≤ N`."

The Weyl element is `ElementaryWeyl.weyl 0 1`, literally the printed word; the
conclusion `N = EL₂(R)` is the lemma's statement. -/
theorem manuscriptSentence_rankTwoUpperAndLowerRoots (v w a b : R)
    (hwv : w * v = 1) (hba : b * a = 1) (hbv : b * v = 0) :
    (∀ r : R, upperRoot r = upperRoot (v * w * r) * upperRoot (fIdem v w * r) ∧
      upperRoot r ∈ printedN v b) ∧
    ElementaryWeyl.weyl (S := R) (0 : Fin 2) 1 (by decide)
      = upperRoot 1 * lowerRoot (-1) * upperRoot 1 ∧
    (∀ r : R, lowerRoot r ∈ printedN v b) ∧
    printedN v b = ⊤ := by
  have hup : ∀ r : R, upperRoot r = upperRoot (v * w * r) * upperRoot (fIdem v w * r) ∧
      upperRoot r ∈ printedN v b := by
    intro r
    have hsplit : upperRoot (v * w * r) * upperRoot (fIdem v w * r) = upperRoot r := by
      rw [upperRoot_mul]
      congr 1
      show v * w * r + (1 - v * w) * r = r
      noncomm_ring
    refine ⟨hsplit.symm, ?_⟩
    rw [← hsplit]
    have hv : upperRoot (v * w * r) ∈ printedN v b := by
      rw [mul_assoc]
      exact (manuscriptSentence_rankTwoCommutatorUpperRoot v a b hbv hba (w * r)).2.2
    exact (printedN v b).mul_mem hv (upperRoot_f_mem_printedN v w a b hwv hbv hba r)
  refine ⟨hup, rfl, fun r ↦ ?_, normalClosure_gen_eq_top v w a b hwv hba hbv⟩
  have hmemconj : ElementaryWeyl.weyl (S := R) (0 : Fin 2) 1 (by decide) * upperRoot r *
      (ElementaryWeyl.weyl (S := R) (0 : Fin 2) 1 (by decide))⁻¹ ∈ printedN v b :=
    (printedN_normal v b).conj_mem _ (hup r).2 _
  rcases ElementaryWeyl.weyl_conj_elGen (S := R) (0 : Fin 2) 1 (by decide)
    (p := 0) (q := 1) (by decide)
    (Equiv.swap_apply_left (0 : Fin 2) 1)
    (Equiv.swap_apply_right (0 : Fin 2) 1) (by decide) r with h | h
  · rw [show lowerRoot r = ElementaryWeyl.weyl (S := R) (0 : Fin 2) 1 (by decide) *
      upperRoot r * (ElementaryWeyl.weyl (S := R) (0 : Fin 2) 1 (by decide))⁻¹ from h.symm]
    exact hmemconj
  · have hneg : lowerRoot (-r) ∈ printedN v b := by
      rw [show lowerRoot (-r) = ElementaryWeyl.weyl (S := R) (0 : Fin 2) 1 (by decide) *
        upperRoot r * (ElementaryWeyl.weyl (S := R) (0 : Fin 2) 1 (by decide))⁻¹ from h.symm]
      exact hmemconj
    have hinv : lowerRoot r = (lowerRoot (-r))⁻¹ := by
      rw [lowerRoot_neg, inv_inv]
    rw [hinv]
    exact (printedN v b).inv_mem hneg

end RankTwoPrintedSteps
end NonMFSentences
end Manuscript
end GroupApproximation

open GroupApproximation.Manuscript.NonMFSentences.RankTwoPrintedSteps

#audit_axioms commutator_gen_mem_printedN
#audit_axioms manuscriptSentence_rankTwoConjugateRows
#audit_axioms manuscriptSentence_rankTwoGeneratorDiagonal
#audit_axioms manuscriptSentence_rankTwoCommutatorUpperRoot
#audit_axioms manuscriptSentence_rankTwoIdempotentF
#audit_axioms manuscriptSentence_rankTwoSplitAndReduction
#audit_axioms manuscriptSentence_rankTwoDecomposition
#audit_axioms manuscriptSentence_rankTwoMultiplicationTable
#audit_axioms manuscriptSentence_rankTwoSixTransvectionWord
#audit_axioms manuscriptSentence_rankTwoConjugationIntoN
#audit_axioms upperRoot_f_mem_printedN
#audit_axioms manuscriptSentence_rankTwoUpperAndLowerRoots
