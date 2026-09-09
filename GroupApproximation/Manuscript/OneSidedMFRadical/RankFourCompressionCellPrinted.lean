import GroupApproximation.Leavitt.OneSidedCompressorDefect
import GroupApproximation.Meta.AxiomGuard

/-!
# Lemma `lem:ring-compression-cell`, in full

`non_mf_groups_exist.tex`, Section `sec:one-sided-inverses`, the printed
statement of the lemma labelled `lem:ring-compression-cell`
(`non_mf_groups_exist.tex` around line 862):

> Let `R` be a unital ring, let `s, t ∈ R` satisfy `t s = 1`, and put
> `e = 1 - s t`.  In `G = EL₄(R)` let `L = EL₃(R)` occupy coordinates
> `1, 2, 3`.  There are `u, c ∈ G` with `u L u⁻¹ ≤ L` and `c ∈ C_G(L)` such
> that `u c u⁻¹ = e₁₂(e)`, `[u c u⁻¹, e₂₃(1)] = e₁₃(e)`.  Every off-diagonal
> entry of a matrix in `u L u⁻¹` has the form `s a t` with `a ∈ R`.

The lemma carries no `\leanverified` badge in the printed manuscript.  The
first four clauses are already proved, over an arbitrary unital ring and
using only `t s = 1`, in `GroupApproximation.Leavitt.OneSidedCompressor` and
`GroupApproximation.Leavitt.OneSidedCompressorDefect`: `compressor`,
`centralMark`, `compressor_compresses_core`, `centralMark_commute_core`,
`compressor_conj_centralMark` and `defect_eq`.

The last clause -- "every off-diagonal entry of a matrix in `u L u⁻¹` has the
form `s a t`" -- is new.  It is not a statement about the *generators*
`e_ij(a)` of `L` (for those, `compressor_conj_root` already gives the exact
value `u e_ij(a) u⁻¹ = e_ij(s a t)`); it is a statement about *every* element
of the subgroup `u L u⁻¹`, i.e. about arbitrary finite products of such
generators and their inverses.  The proof is the closure induction the
printed sentence gestures at: the set `s R t = {s a t : a ∈ R}` is closed
under addition, negation and multiplication (the last using `t s = 1`:
`(s a t)(s b t) = s a (t s) b t = s (a b) t`), so it plays the role of a
(possibly non-unital) subring, and the elementary matrices with entries in
`s R t` generate a set of matrices of the shape `1 + N` with every entry of
`N` -- diagonal included -- again in `s R t`.  Tracking `N` for both `g` and
`g⁻¹` together lets the `inv` case of `Subgroup.closure_induction` close
without a general matrix-inversion argument.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace RankFourCompressionCellPrinted

open OneSidedCompressor
open scoped commutatorElement

section Sandwich

variable {R : Type} [Ring R] (P : OneSidedInverse R)

/-- The printed sandwich form `s a t`, with `a` ranging over `R`. -/
def IsSandwich (x : R) : Prop := ∃ a : R, x = P.s * a * P.t

theorem isSandwich_zero : IsSandwich P 0 := ⟨0, by simp⟩

theorem isSandwich_add {x y : R} (hx : IsSandwich P x) (hy : IsSandwich P y) :
    IsSandwich P (x + y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a + b, by simp [mul_add, add_mul]⟩

theorem isSandwich_neg {x : R} (hx : IsSandwich P x) : IsSandwich P (-x) := by
  obtain ⟨a, rfl⟩ := hx
  exact ⟨-a, by simp [mul_neg, neg_mul]⟩

/-- The multiplicative closure `s R t · s R t ⊆ s R t`, using `t s = 1`. -/
theorem isSandwich_mul {x y : R} (hx : IsSandwich P x) (hy : IsSandwich P y) :
    IsSandwich P (x * y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a * b, by simp [mul_assoc, P.assoc_t_mul_s]⟩

/-- `IsSandwich` is closed under arbitrary finite sums. -/
theorem isSandwich_sum {ι : Type*} (s : Finset ι) (f : ι → R)
    (hf : ∀ i ∈ s, IsSandwich P (f i)) : IsSandwich P (∑ i ∈ s, f i) :=
  Finset.sum_induction f (IsSandwich P)
    (fun _ _ hx hy => isSandwich_add P hx hy) (isSandwich_zero P) hf

end Sandwich

section Induction

variable {R : Type} [Ring R] (P : OneSidedInverse R)

/-- Shorthand for the matrix of a rank-four elementary group element. -/
def matOf (g : elementaryGroup (Fin 4) R) : Matrix (Fin 4) (Fin 4) R :=
  (↑(↑g : (Matrix (Fin 4) (Fin 4) R)ˣ) : Matrix (Fin 4) (Fin 4) R)

theorem matOf_eq (g : elementaryGroup (Fin 4) R) :
    matOf g = (↑(↑g : (Matrix (Fin 4) (Fin 4) R)ˣ) : Matrix (Fin 4) (Fin 4) R) := rfl

@[simp] theorem matOf_mul (g h : elementaryGroup (Fin 4) R) :
    matOf (g * h) = matOf g * matOf h := by
  simp [matOf_eq]

@[simp] theorem matOf_one : matOf (1 : elementaryGroup (Fin 4) R) = 1 := by
  simp [matOf_eq]

theorem matOf_elementaryRoot (i j : Fin 4) (hij : i ≠ j) (a : R) :
    matOf (elementaryRoot i j hij a) = 1 + Matrix.single i j a := by
  simp only [matOf_eq, elementaryRoot_val]
  rfl

/-- The internal induction invariant: `u g u⁻¹` differs from the identity by
a matrix `N` that vanishes on the spare row and column (so `u g u⁻¹` never
leaves the core, matching `compressor_compresses_core`) and is a sandwich
everywhere, diagonal entries included. -/
def ConjInv (g : elementaryGroup (Fin 4) R) : Prop :=
  ∃ N : Matrix (Fin 4) (Fin 4) R,
    matOf (compressor P * g * (compressor P)⁻¹) = 1 + N ∧
      (∀ k : Fin 4, N k lastIdx = 0) ∧ (∀ k : Fin 4, N lastIdx k = 0) ∧
      ∀ k l : Fin 4, IsSandwich P (N k l)

/-- The paired invariant for `g` and `g⁻¹`, tracked together so that the
`inv` case of `Subgroup.closure_induction` closes by swapping the two
halves. -/
def ConjInvPair (g : elementaryGroup (Fin 4) R) : Prop :=
  ConjInv P g ∧ ConjInv P g⁻¹

theorem conjInv_coreGenerator (i j : Fin 3) (hij : i ≠ j) (a : R) :
    ConjInv P (elementaryRoot (coreIdx i) (coreIdx j) (coreIdx_injective.ne hij) a) := by
  refine ⟨Matrix.single (coreIdx i) (coreIdx j) (P.s * a * P.t), ?_, ?_, ?_, ?_⟩
  · rw [compressor_conj_root P i j hij a]
    exact matOf_elementaryRoot _ _ _ _
  · intro k
    rw [Matrix.single_apply]
    have h : coreIdx j ≠ lastIdx := coreIdx_ne_last j
    simp [h]
  · intro k
    rw [Matrix.single_apply]
    have h : coreIdx i ≠ lastIdx := coreIdx_ne_last i
    simp [h]
  · intro k l
    rw [Matrix.single_apply]
    split_ifs with h
    · exact ⟨a, rfl⟩
    · exact isSandwich_zero P

theorem conjInvPair_mem {x : elementaryGroup (Fin 4) R} (hx : x ∈ coreRootSet R) :
    ConjInvPair P x := by
  obtain ⟨i, j, hij, a, rfl⟩ := hx
  refine ⟨conjInv_coreGenerator P i j hij a, ?_⟩
  rw [← elementaryRoot_neg]
  exact conjInv_coreGenerator P i j hij (-a)

theorem conjInv_mul {x y : elementaryGroup (Fin 4) R}
    (hx : ConjInv P x) (hy : ConjInv P y) : ConjInv P (x * y) := by
  obtain ⟨N1, hM1, hN1a, hN1b, hN1S⟩ := hx
  obtain ⟨N2, hM2, hN2a, hN2b, hN2S⟩ := hy
  refine ⟨N1 + N2 + N1 * N2, ?_, ?_, ?_, ?_⟩
  · have hgroup : compressor P * (x * y) * (compressor P)⁻¹ =
        compressor P * x * (compressor P)⁻¹ *
          (compressor P * y * (compressor P)⁻¹) := by group
    rw [hgroup, matOf_mul, hM1, hM2]
    noncomm_ring
  · intro k
    have h1 : (N1 * N2) k lastIdx = 0 := by
      rw [Matrix.mul_apply]
      exact Finset.sum_eq_zero fun m _ => by rw [hN2a m, mul_zero]
    simp [Matrix.add_apply, hN1a k, hN2a k, h1]
  · intro k
    have h1 : (N1 * N2) lastIdx k = 0 := by
      rw [Matrix.mul_apply]
      exact Finset.sum_eq_zero fun m _ => by rw [hN1b m, zero_mul]
    simp [Matrix.add_apply, hN1b k, hN2b k, h1]
  · intro k l
    have hN12 : IsSandwich P ((N1 * N2) k l) := by
      rw [Matrix.mul_apply]
      exact isSandwich_sum P Finset.univ (fun m => N1 k m * N2 m l)
        (fun m _ => isSandwich_mul P (hN1S k m) (hN2S m l))
    simp only [Matrix.add_apply]
    exact isSandwich_add P (isSandwich_add P (hN1S k l) (hN2S k l)) hN12

theorem conjInvPair_of_mem {g : elementaryGroup (Fin 4) R} (hg : g ∈ core R) :
    ConjInvPair P g := by
  rw [core] at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact conjInvPair_mem P hx
  | one =>
      have h1 : ConjInv P (1 : elementaryGroup (Fin 4) R) := by
        refine ⟨0, ?_, ?_, ?_, ?_⟩
        · simp [matOf_eq]
        · intro k; simp
        · intro k; simp
        · intro k l; simp only [Matrix.zero_apply]; exact isSandwich_zero P
      refine ⟨h1, ?_⟩
      rw [inv_one]
      exact h1
  | mul x y _ _ ihx ihy =>
      refine ⟨conjInv_mul P ihx.1 ihy.1, ?_⟩
      rw [mul_inv_rev]
      exact conjInv_mul P ihy.2 ihx.2
  | inv x _ ihx =>
      refine ⟨ihx.2, ?_⟩
      rw [inv_inv]
      exact ihx.1

/-- **The off-diagonal clause of `lem:ring-compression-cell`, for a single
conjugate.**  Every off-diagonal entry of `u g u⁻¹`, for `g` in the core, has
the printed sandwich form `s a t`. -/
theorem compressor_conj_core_offDiag_sandwich {g : elementaryGroup (Fin 4) R}
    (hg : g ∈ core R) (i j : Fin 4) (hij : i ≠ j) :
    ∃ a : R, matOf (compressor P * g * (compressor P)⁻¹) i j = P.s * a * P.t := by
  obtain ⟨N, hM, _, _, hS⟩ := (conjInvPair_of_mem P hg).1
  obtain ⟨a, ha⟩ := hS i j
  refine ⟨a, ?_⟩
  rw [hM, Matrix.add_apply, Matrix.one_apply_ne hij, zero_add]
  exact ha

end Induction

/-- **Lemma `lem:ring-compression-cell`, exactly as printed, with every
clause proved.**  For every unital ring `R` and `s, t ∈ R` with `t s = 1`, in
`G = EL₄(R)` with the core `L = EL₃(R)` on coordinates `1, 2, 3`
(zero-indexed here as `0, 1, 2`), there are `u, c ∈ G` (automatic, since `G`
is the ambient type) with `u L u⁻¹ ≤ L`, `c ∈ C_G(L)`, `u c u⁻¹ = e₁₂(e)`,
`[u c u⁻¹, e₂₃(1)] = e₁₃(e)`, and every off-diagonal entry of a matrix in
`u L u⁻¹` has the printed form `s a t` with `a ∈ R`. -/
def PrintedRankFourCompressionCell : Prop :=
  ∀ (R : Type) [Ring R] (P : OneSidedInverse R),
    ∃ u c : elementaryGroup (Fin 4) R,
      (∀ g ∈ core R, u * g * u⁻¹ ∈ core R) ∧
        (∀ g ∈ core R, Commute c g) ∧
        u * c * u⁻¹ =
          elementaryRoot (coreIdx 0) (coreIdx 1) (coreIdx_injective.ne zeroNeOne)
            P.e ∧
        ⁅u * c * u⁻¹, printedEll R⁆ = printedDefectRoot P ∧
        ∀ g ∈ core R, ∀ i j : Fin 4, i ≠ j →
          ∃ a : R,
            (↑(↑(u * g * u⁻¹) : (Matrix (Fin 4) (Fin 4) R)ˣ) :
                Matrix (Fin 4) (Fin 4) R) i j = P.s * a * P.t

theorem manuscriptRankFourCompressionCell : PrintedRankFourCompressionCell := by
  intro R _ P
  exact ⟨compressor P, centralMark P, compressor_compresses_core P,
    centralMark_commute_core P, compressor_conj_centralMark P, defect_eq P,
    fun g hg i j hij =>
      compressor_conj_core_offDiag_sandwich P hg i j hij⟩

end RankFourCompressionCellPrinted
end OneSidedMFRadical
end Manuscript
end GroupApproximation

open GroupApproximation
open GroupApproximation.Manuscript.OneSidedMFRadical

#audit_closed_axioms
  RankFourCompressionCellPrinted.manuscriptRankFourCompressionCell
