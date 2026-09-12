import GroupApproximation.Manuscript.OneSidedMFRadical.RankFourCompressionCellPrinted
import GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingFullIdeal
import GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingSimple
import GroupApproximation.Meta.AxiomGuard

/-!
# The two corollaries of `thm:full-defect-ring`: the printed proof steps

`non_mf_groups_exist.tex`, the proofs of `cor:simple-infinite-ring` (tex 1026-1036)
and `cor:one-sided-ring-maximal` (tex 1050-1058) at origin/main `73c867c5b`.
`Manuscript/NonMFSentences/OneSidedSentences.lean` carries the conclusions of these
proofs; this module carries the printed reasons they give:

* "then `1-st` is a nonzero idempotent" (`manuscriptSentence_simpleCaseIdempotentFull`);
* "then `1-s₁t₁ = ∑_{i≥2}sᵢtᵢ` and `t₂(1-s₁t₁)s₂ = 1`"
  (`manuscriptSentence_leavittCaseSandwich`), from the printed relations
  `tᵢsⱼ = δᵢⱼ`, `∑ᵢsᵢtᵢ = 1` alone;
* "the compression is strict, since `e(sat) = 0` while `e·1 = e ≠ 0` puts `e₁₂(1)` in
  `L ∖ uLu⁻¹`" (`manuscriptSentence_strictCompressionWitness`), using the last
  assertion of `lem:ring-compression-cell` (every off-diagonal entry of `uLu⁻¹` has
  the form `sat`).
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMFSentences
namespace OneSidedCorollarySentences

open GroupApproximation.OneSidedCompressor
open GroupApproximation.Manuscript.OneSidedMFRadical.RankFourCompressionCellPrinted
open GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRing

/-- **Printed (tex 1027-1029).**  "In the first case choose `ts = 1 ≠ st`; then
`1-st` is a nonzero idempotent, and since `R` is simple it generates `R` as a
two-sided ideal." -/
theorem manuscriptSentence_simpleCaseIdempotentFull {R : Type*} [Ring R] [IsSimpleRing R]
    (hdf : ¬ IsDedekindFiniteMonoid R) :
    ∃ s t : R, t * s = 1 ∧ s * t ≠ 1 ∧
      (1 - s * t) * (1 - s * t) = 1 - s * t ∧ 1 - s * t ≠ 0 ∧
      ∃ (m : ℕ) (a b : Fin m → R), ∑ k, a k * (1 - s * t) * b k = 1 := by
  obtain ⟨s, t, hts, hst⟩ := exists_oneSidedInverse_of_not_isDedekindFinite hdf
  refine ⟨s, t, hts, hst, ?_, sub_ne_zero_of_ne fun h ↦ hst h.symm,
    (isSimpleRing_full_of_not_directlyFinite hts hst).2⟩
  have h : s * t * (s * t) = s * t := by
    rw [mul_assoc, ← mul_assoc t, hts, one_mul]
  calc (1 - s * t) * (1 - s * t) = 1 - s * t - s * t + s * t * (s * t) := by noncomm_ring
    _ = 1 - s * t := by rw [h]; abel

/-- **Printed (tex 1029-1034).**  "In the second case, with generators
`s₁,…,s_m,t₁,…,t_m` subject to `tᵢsⱼ = δᵢⱼ` and `∑ᵢsᵢtᵢ = 1`, take `s = s₁` and
`t = t₁`; then `1-s₁t₁ = ∑_{i≥2}sᵢtᵢ` and `t₂(1-s₁t₁)s₂ = 1`."

For any complete matrix family `F` with `m ≥ 2` members (zero-based: `s₁ = F.left 0`,
`t₁ = F.right 0`, `s₂ = F.left 1`, `t₂ = F.right 1`). -/
theorem manuscriptSentence_leavittCaseSandwich {A : Type*} [Ring A] {m : ℕ} (hm : 2 ≤ m)
    (F : CompleteMatrixFamily A (Fin m)) :
    F.right ⟨0, by omega⟩ * F.left ⟨0, by omega⟩ = 1 ∧
    1 - F.left ⟨0, by omega⟩ * F.right ⟨0, by omega⟩
      = ∑ i ∈ Finset.univ.erase (⟨0, by omega⟩ : Fin m), F.left i * F.right i ∧
    F.right ⟨1, by omega⟩ * (1 - F.left ⟨0, by omega⟩ * F.right ⟨0, by omega⟩)
      * F.left ⟨1, by omega⟩ = 1 := by
  have h00 : F.right ⟨0, by omega⟩ * F.left ⟨0, by omega⟩ = 1 := by
    rw [F.orthogonal, if_pos rfl]
  have h11 : F.right ⟨1, by omega⟩ * F.left ⟨1, by omega⟩ = 1 := by
    rw [F.orthogonal, if_pos rfl]
  have h10 : F.right ⟨1, by omega⟩ * F.left ⟨0, by omega⟩ = 0 := by
    rw [F.orthogonal, if_neg (by simp)]
  refine ⟨h00, ?_, ?_⟩
  · have hc := F.complete
    rw [← Finset.add_sum_erase Finset.univ (fun i ↦ F.left i * F.right i)
      (Finset.mem_univ (⟨0, by omega⟩ : Fin m))] at hc
    rw [← hc]
    abel
  · calc F.right ⟨1, by omega⟩ * (1 - F.left ⟨0, by omega⟩ * F.right ⟨0, by omega⟩)
          * F.left ⟨1, by omega⟩
        = F.right ⟨1, by omega⟩ * F.left ⟨1, by omega⟩
          - F.right ⟨1, by omega⟩ * F.left ⟨0, by omega⟩
            * (F.right ⟨0, by omega⟩ * F.left ⟨1, by omega⟩) := by noncomm_ring
      _ = 1 := by rw [h11, h10, zero_mul, sub_zero]

/-- **Printed (tex 1053-1056).**  "and the compression is strict, since `e(sat) = 0`
while `e·1 = e ≠ 0` puts `e₁₂(1)` in `L ∖ uLu⁻¹`."

Over any ring `S` with `ts = 1` and `e = 1-st ≠ 0`, in `EL₄(S)` with `L = EL₃(S)` on
the first three coordinates and `u` the compressor of `lem:ring-compression-cell`:
`e` kills every `sat`, `e₁₂(1) ∈ L`, and `e₁₂(1)` is no conjugate `ugu⁻¹` with `g ∈ L`,
because the `(1,2)` entry of such a conjugate has the form `sat`. -/
theorem manuscriptSentence_strictCompressionWitness {S : Type} [Ring S]
    (P : OneSidedInverse S) (he : P.e ≠ 0) :
    (∀ a : S, P.e * (P.s * a * P.t) = 0) ∧ P.e * 1 = P.e ∧
    elementaryRoot (coreIdx 0) (coreIdx 1) (coreIdx_injective.ne zeroNeOne) (1 : S) ∈ core S ∧
    ∀ g ∈ core S, compressor P * g * (compressor P)⁻¹
      ≠ elementaryRoot (coreIdx 0) (coreIdx 1) (coreIdx_injective.ne zeroNeOne) (1 : S) := by
  have hkill : ∀ a : S, P.e * (P.s * a * P.t) = 0 := by
    intro a
    rw [← mul_assoc, ← mul_assoc, P.e_mul_s, zero_mul, zero_mul]
  refine ⟨hkill, mul_one _, elementaryRoot_mem_core 0 1 zeroNeOne 1, fun g hg heq ↦ he ?_⟩
  obtain ⟨a, ha⟩ := compressor_conj_core_offDiag_sandwich P hg (coreIdx 0) (coreIdx 1)
    (coreIdx_injective.ne zeroNeOne)
  rw [heq, matOf_elementaryRoot] at ha
  have h1 : (1 : S) = P.s * a * P.t := by
    simpa [Matrix.one_apply_ne (coreIdx_injective.ne zeroNeOne)] using ha
  have h2 := hkill a
  rw [← h1, mul_one] at h2
  exact h2

end OneSidedCorollarySentences
end NonMFSentences
end Manuscript
end GroupApproximation

open GroupApproximation.Manuscript.NonMFSentences.OneSidedCorollarySentences

#audit_axioms manuscriptSentence_simpleCaseIdempotentFull
#audit_axioms manuscriptSentence_leavittCaseSandwich
#audit_axioms manuscriptSentence_strictCompressionWitness
