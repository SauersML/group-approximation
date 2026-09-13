import GroupApproximation.Leavitt.OneSidedCompressorDefect
import GroupApproximation.Meta.AxiomGuard

/-!
# Four sentences of the proof of `lem:ring-compression-cell`, over every unital ring

`non_mf_groups_exist.tex`, Section `sec:one-sided-inverses`, Lemma `lem:ring-compression-cell`
(tex lines 855–869) and its proof (tex lines 871–912):

> Let `R` be a unital ring, let `s,t ∈ R` satisfy `ts = 1`, and put `e = 1 - st`.  In
> `G = EL₄(R)` let `L = EL₃(R)` occupy coordinates `1,2,3`.

The census carriers of four sentences of this proof,
`FullDefectRingSentences.manuscriptSentence_compressorPieceDef`,
`manuscriptSentence_compressorInvertible`, `manuscriptSentence_centralMark` and
`manuscriptSentence_centralMarkCentral`, are stated only for the universal pair
`UniversalPair.pairInverse` over the one ring `UniversalPair.UniversalPairRing`.  The lemma is
printed for every unital ring.  This module states the four sentences for every ring `R` and
every `P : OneSidedInverse R`, a pair `s, t ∈ R` with `ts = 1`, and proves them from the general
lemmas of `GroupApproximation.Leavitt.OneSidedCompressor` and `OneSidedCompressorDefect`.

Coordinates are 0-indexed: the printed `i ∈ {1,2,3}` is `coreIdx i` with `i : Fin 3`, and the
printed `4` is `lastIdx`.

* `printedCompressorPieces` (tex 872–875): the definition of `uᵢ`.
* `printedCompressorInvertible` (tex 876–888): `u = u₃u₂u₁` is the displayed matrix, and that
  matrix is invertible because `u` is a product of elementary matrices.
* `printedCentralMark` (tex 899–903): `c = [e₄₁(e), e₁₄(t)] = diag(1,1,1,1+et)`.
* `printedCentralMarkCentral` (tex 904–906): a diagonal matrix of this shape commutes with every
  `diag(A,1)`, so `c ∈ C_G(L)`.  The proof follows the printed route.  Every element of `L` has
  the shape `diag(A,1)` (`core_isBlockDiagOne`), `diag(1,1,1,1+et)` commutes with every matrix
  of that shape (`centralMarkMatrix_commute_blockDiagOne`), and the value of `c` is
  `OneSidedCompressor.centralMark_val`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace RingCompressionCellGeneral

open OneSidedCompressor
open scoped commutatorElement

universe u

section BlockShape

variable {R : Type u} [Ring R]

/-- The shape `diag(A,1)` of a `4 × 4` matrix: off the diagonal its last row and last column
vanish, and its corner entry is `1`. -/
def IsBlockDiagOne (M : Matrix (Fin 4) (Fin 4) R) : Prop :=
  (∀ k : Fin 4, k ≠ lastIdx → M k lastIdx = 0 ∧ M lastIdx k = 0) ∧ M lastIdx lastIdx = 1

theorem isBlockDiagOne_one : IsBlockDiagOne (1 : Matrix (Fin 4) (Fin 4) R) :=
  ⟨fun _ hk => ⟨Matrix.one_apply_ne hk, Matrix.one_apply_ne hk.symm⟩, Matrix.one_apply_eq _⟩

theorem IsBlockDiagOne.mul {M N : Matrix (Fin 4) (Fin 4) R}
    (hM : IsBlockDiagOne M) (hN : IsBlockDiagOne N) : IsBlockDiagOne (M * N) := by
  obtain ⟨hMo, hMc⟩ := hM
  obtain ⟨hNo, hNc⟩ := hN
  refine ⟨fun k hk => ⟨?_, ?_⟩, ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : j = lastIdx
    · rw [hj, (hMo k hk).1, zero_mul]
    · rw [(hNo j hj).1, mul_zero]
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : j = lastIdx
    · rw [hj, (hNo k hk).2, mul_zero]
    · rw [(hMo j hj).2, zero_mul]
  · rw [Matrix.mul_apply, Finset.sum_eq_single lastIdx]
    · rw [hMc, hNc, mul_one]
    · intro j _ hj
      rw [(hMo j hj).2, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h

/-- A root `e_{ij}(a)` with `1 ≤ i ≠ j ≤ 3` has the shape `diag(A,1)`. -/
theorem elementaryRoot_isBlockDiagOne (i j : Fin 3) (hij : i ≠ j) (a : R) :
    IsBlockDiagOne
      (↑(↑(elementaryRoot (coreIdx i) (coreIdx j) (coreIdx_injective.ne hij) a) :
          (Matrix (Fin 4) (Fin 4) R)ˣ) : Matrix (Fin 4) (Fin 4) R) := by
  change IsBlockDiagOne (1 + Matrix.single (coreIdx i) (coreIdx j) a)
  refine ⟨fun k hk => ⟨?_, ?_⟩, ?_⟩
  · first
      | rw [Matrix.add_apply, Matrix.one_apply_ne hk,
          Matrix.single_apply_of_ne (fun h => coreIdx_ne_last j h.2), add_zero]
      | simp [Matrix.single, Matrix.one_apply_ne hk, coreIdx_ne_last j]
  · first
      | rw [Matrix.add_apply, Matrix.one_apply_ne hk.symm,
          Matrix.single_apply_of_ne (fun h => coreIdx_ne_last i h.1), add_zero]
      | simp [Matrix.single, Matrix.one_apply_ne hk.symm, coreIdx_ne_last i]
  · first
      | rw [Matrix.add_apply, Matrix.one_apply_eq,
          Matrix.single_apply_of_ne (fun h => coreIdx_ne_last i h.1), add_zero]
      | simp [Matrix.single, coreIdx_ne_last i]

/-- **Every element of `L = EL₃(R)` has the shape `diag(A,1)`.** -/
theorem core_isBlockDiagOne (g : elementaryGroup (Fin 4) R) (hg : g ∈ core R) :
    IsBlockDiagOne (↑(↑g : (Matrix (Fin 4) (Fin 4) R)ˣ) : Matrix (Fin 4) (Fin 4) R) := by
  rw [core] at hg
  induction hg using Subgroup.closure_induction'' with
  | mem x hx =>
      obtain ⟨i, j, hij, a, rfl⟩ := hx
      exact elementaryRoot_isBlockDiagOne i j hij a
  | inv_mem x hx =>
      obtain ⟨i, j, hij, a, rfl⟩ := hx
      rw [← elementaryRoot_neg]
      exact elementaryRoot_isBlockDiagOne i j hij (-a)
  | one => exact isBlockDiagOne_one
  | mul x y _ _ hx hy => exact hx.mul hy

/-- The printed value `diag(1,1,1,1+et)` as a diagonal matrix. -/
theorem centralMarkMatrix_eq_diagonal (P : OneSidedInverse R) :
    centralMarkMatrix P = Matrix.diagonal ![1, 1, 1, 1 + P.e * P.t] := by
  ext r c
  fin_cases r <;> fin_cases c <;> simp [centralMarkMatrix, Matrix.diagonal]

/-- **A diagonal matrix of this shape commutes with every `diag(A,1)`.** -/
theorem centralMarkMatrix_commute_blockDiagOne (P : OneSidedInverse R)
    {M : Matrix (Fin 4) (Fin 4) R} (hM : IsBlockDiagOne M) :
    centralMarkMatrix P * M = M * centralMarkMatrix P := by
  obtain ⟨hoff, hcorner⟩ := hM
  have hd : ∀ k : Fin 4, k ≠ lastIdx → (![1, 1, 1, 1 + P.e * P.t] : Fin 4 → R) k = 1 := by
    intro k hk
    fin_cases k
    · simp
    · simp
    · simp
    · exact absurd (by decide) hk
  rw [centralMarkMatrix_eq_diagonal]
  ext r c
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hr : r = lastIdx <;> by_cases hc : c = lastIdx
  · subst hr
    subst hc
    rw [hcorner, one_mul, mul_one]
  · subst hr
    rw [(hoff c hc).2, mul_zero, zero_mul]
  · subst hc
    rw [(hoff r hr).1, mul_zero, zero_mul]
  · rw [hd r hr, hd c hc, one_mul, mul_one]

/-- `c ∈ C_G(L)` along the printed route: `c = diag(1,1,1,1+et)` commutes with every
`diag(A,1)`, and every element of `L` is one. -/
theorem centralMark_commute_core_blockRoute (P : OneSidedInverse R) :
    ∀ g ∈ core R, Commute (centralMark P) g := by
  intro g hg
  have h := centralMarkMatrix_commute_blockDiagOne P (core_isBlockDiagOne g hg)
  rw [← centralMark_val P] at h
  apply Subtype.ext
  apply Units.ext
  exact h

end BlockShape

/-- **Printed sentence** (tex 872–875, proof of `lem:ring-compression-cell`).

> For `i=1,2,3`, set `u_i=e_{4i}(t-1)e_{i4}(1)e_{4i}(s-1)e_{i4}(-t)`.

The lemma is printed for a unital ring `R` and `s,t ∈ R` with `ts=1`, which is
`P : OneSidedInverse R`.  The printed `i` is `coreIdx i` and the printed `4` is `lastIdx`. -/
def PrintedCompressorPieces : Prop :=
  ∀ (R : Type u) [Ring R] (P : OneSidedInverse R) (i : Fin 3),
    compressorPiece P i =
      elementaryRoot lastIdx (coreIdx i) (last_ne_coreIdx i) (P.t - 1) *
        elementaryRoot (coreIdx i) lastIdx (coreIdx_ne_last i) 1 *
          elementaryRoot lastIdx (coreIdx i) (last_ne_coreIdx i) (P.s - 1) *
            elementaryRoot (coreIdx i) lastIdx (coreIdx_ne_last i) (-P.t)

theorem printedCompressorPieces : PrintedCompressorPieces := by
  intro R _ P i
  rfl

/-- **Printed sentence** (tex 876–888).

> Its block on coordinates `(i,4)` is `(s e; 0 t)`, so `u=u_3u_2u_1∈EL_4(R)` is the matrix
> `(s 0 0 e; 0 s 0 et; 0 0 s et²; 0 0 0 t³)`, invertible as a product of elementary matrices.

`u` is the product `u₃u₂u₁` in `EL₄(R)`, its matrix is the display `compressorMatrix P`
(`OneSidedCompressor.compressor_val`), and the display is invertible because it is the matrix of
the element `u` of `EL₄(R) ≤ GL₄(R)`. -/
def PrintedCompressorInvertible : Prop :=
  ∀ (R : Type u) [Ring R] (P : OneSidedInverse R),
    compressor P = compressorPiece P 2 * compressorPiece P 1 * compressorPiece P 0 ∧
      (↑(↑(compressor P) : (Matrix (Fin 4) (Fin 4) R)ˣ) : Matrix (Fin 4) (Fin 4) R) =
        !![P.s, 0, 0, P.e;
           0, P.s, 0, P.e * P.t;
           0, 0, P.s, P.e * P.t * P.t;
           0, 0, 0, P.t * P.t * P.t] ∧
      IsUnit (!![P.s, 0, 0, P.e;
                 0, P.s, 0, P.e * P.t;
                 0, 0, P.s, P.e * P.t * P.t;
                 0, 0, 0, P.t * P.t * P.t] : Matrix (Fin 4) (Fin 4) R)

theorem printedCompressorInvertible : PrintedCompressorInvertible := by
  intro R _ P
  refine ⟨rfl, compressor_val P, ?_⟩
  change IsUnit (compressorMatrix P)
  rw [← compressor_val P]
  exact Units.isUnit _

/-- **Printed sentence** (tex 899–903).

> The element `c=[e_{41}(e),e_{14}(t)]=diag(1,1,1,1+et)` -/
def PrintedCentralMark : Prop :=
  ∀ (R : Type u) [Ring R] (P : OneSidedInverse R),
    centralMark P =
        ⁅elementaryRoot lastIdx (coreIdx 0) (last_ne_coreIdx 0) P.e,
          elementaryRoot (coreIdx 0) lastIdx (coreIdx_ne_last 0) P.t⁆ ∧
      (↑(↑(centralMark P) : (Matrix (Fin 4) (Fin 4) R)ˣ) : Matrix (Fin 4) (Fin 4) R) =
        !![1, 0, 0, 0;
           0, 1, 0, 0;
           0, 0, 1, 0;
           0, 0, 0, 1 + P.e * P.t]

theorem printedCentralMark : PrintedCentralMark := by
  intro R _ P
  exact ⟨centralMark_eq_commutator P, centralMark_val P⟩

/-- **Printed sentence** (tex 904–906).

> is computed in the block on coordinates `(1,4)` using `te=0`, and a diagonal matrix of this
> shape commutes with every `diag(A,1)`, so `c∈C_G(L)`.

The first conjunct is "a diagonal matrix of this shape commutes with every `diag(A,1)`", the
second is the shape `diag(A,1)` of the elements of `L`, and the third is `c ∈ C_G(L)`, proved
from the first two (`centralMark_commute_core_blockRoute`).  The computation of `c` is the
value in `PrintedCentralMark`. -/
def PrintedCentralMarkCentral : Prop :=
  ∀ (R : Type u) [Ring R] (P : OneSidedInverse R),
    (∀ M : Matrix (Fin 4) (Fin 4) R, IsBlockDiagOne M →
        centralMarkMatrix P * M = M * centralMarkMatrix P) ∧
      (∀ g ∈ core R,
        IsBlockDiagOne (↑(↑g : (Matrix (Fin 4) (Fin 4) R)ˣ) : Matrix (Fin 4) (Fin 4) R)) ∧
      ∀ g ∈ core R, Commute (centralMark P) g

theorem printedCentralMarkCentral : PrintedCentralMarkCentral := by
  intro R _ P
  exact ⟨fun _ hM => centralMarkMatrix_commute_blockDiagOne P hM,
    fun g hg => core_isBlockDiagOne g hg, centralMark_commute_core_blockRoute P⟩

end RingCompressionCellGeneral
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.RingCompressionCellGeneral.isBlockDiagOne_one
#audit_axioms GroupApproximation.Manuscript.NonMF.RingCompressionCellGeneral.IsBlockDiagOne.mul
#audit_axioms GroupApproximation.Manuscript.NonMF.RingCompressionCellGeneral.elementaryRoot_isBlockDiagOne
#audit_axioms GroupApproximation.Manuscript.NonMF.RingCompressionCellGeneral.core_isBlockDiagOne
#audit_axioms GroupApproximation.Manuscript.NonMF.RingCompressionCellGeneral.centralMarkMatrix_eq_diagonal
#audit_axioms GroupApproximation.Manuscript.NonMF.RingCompressionCellGeneral.centralMarkMatrix_commute_blockDiagOne
#audit_axioms GroupApproximation.Manuscript.NonMF.RingCompressionCellGeneral.centralMark_commute_core_blockRoute
#audit_closed_axioms GroupApproximation.Manuscript.NonMF.RingCompressionCellGeneral.printedCompressorPieces
#audit_closed_axioms GroupApproximation.Manuscript.NonMF.RingCompressionCellGeneral.printedCompressorInvertible
#audit_closed_axioms GroupApproximation.Manuscript.NonMF.RingCompressionCellGeneral.printedCentralMark
#audit_closed_axioms GroupApproximation.Manuscript.NonMF.RingCompressionCellGeneral.printedCentralMarkCentral
