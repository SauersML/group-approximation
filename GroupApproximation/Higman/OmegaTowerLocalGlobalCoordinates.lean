import GroupApproximation.Higman.OmegaTowerConjugateBasisInvariant
import GroupApproximation.Higman.OmegaTowerDescent

/-!
# From the inner local classifier to the outer global invariant

For positive block width and `0 ∈ B`, a selected window block itself belongs
to `omegaOp m B`: its zeroth block is the original sequence and every other
block is zero.  Consequently the local coordinate subgroup returned by the
inner classifier lies in the global coordinate subgroup preserved by the
outer signed scan.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open Conj Seq

theorem blockAt_zero_eq_self {m : ℕ} {f : E} (hf : f ∈ blockSet m) :
    blockAt m 0 f = f := by
  apply Finsupp.ext
  intro j
  rw [blockAt_apply]
  by_cases hj : j ∈ Finset.Ico (0 : ℤ) (m : ℤ)
  · rw [if_pos hj]
    congr 1
    ring
  · rw [if_neg hj]
    exact (hf j hj).symm

theorem blockAt_eq_zero_of_ne_zero {m : ℕ} (hm : 0 < m) {i : ℤ}
    (hi : i ≠ 0) {f : E} (hf : f ∈ blockSet m) :
    blockAt m i f = 0 := by
  have hmz : 0 < (m : ℤ) := by exact_mod_cast hm
  apply Finsupp.ext
  intro j
  rw [blockAt_apply]
  by_cases hj : j ∈ Finset.Ico (0 : ℤ) (m : ℤ)
  · rw [if_pos hj]
    apply hf
    rw [Finset.mem_Ico] at hj ⊢
    intro hij
    have hi_cases : i ≤ -1 ∨ 1 ≤ i := by omega
    rcases hi_cases with hi_neg | hi_pos
    · have hmul : (m : ℤ) * i ≤ (m : ℤ) * (-1) :=
        mul_le_mul_of_nonneg_left hi_neg hmz.le
      linarith
    · have hmul : (m : ℤ) * 1 ≤ (m : ℤ) * i :=
        mul_le_mul_of_nonneg_left hi_pos hmz.le
      linarith
  · rw [if_neg hj]
    rfl

/-- A selected positive-width window block is a member of the full blockwise
operation when the zero block is allowed. -/
theorem mem_omegaOp_of_mem_inter_blockSet {m : ℕ} (hm : 0 < m)
    {B : Set E} (h0 : (0 : E) ∈ B) {f : E} (hf : f ∈ B ∩ blockSet m) :
    f ∈ omegaOp m B := by
  intro i
  by_cases hi : i = 0
  · subst i
    rw [blockAt_zero_eq_self hf.2]
    exact hf.1
  · rw [blockAt_eq_zero_of_ne_zero hm hi hf.2]
    exact h0

/-- The local `K`-subgroup found by the inner classifier is contained in the
global `omegaOp` index subgroup. -/
theorem localKSub_le_omegaKSub {m : ℕ} (hm : 0 < m) {B : Set E}
    (h0 : (0 : E) ∈ B) : localKSub m B ≤ omegaKSub m B := by
  apply Subgroup.closure_mono
  rintro _ ⟨f, hf, rfl⟩
  exact ⟨f, mem_omegaOp_of_mem_inter_blockSet hm h0 hf, rfl⟩

/-- The exact local free-coordinate subgroup returned by the inner
classifier seeds the invariant used by the outer scan. -/
theorem localCoordSub_le_omegaCoordSub {m : ℕ} (hm : 0 < m) {B : Set E}
    (h0 : (0 : E) ∈ B) : localCoordSub m B ≤ omegaCoordSub m B := by
  unfold localCoordSub omegaCoordSub
  apply Subgroup.closure_mono
  exact Set.image_mono (localKSub_le_omegaKSub hm h0)

/-- After either signed outer pinch, an inner-classified local coordinate
word lies in the global invariant. -/
theorem signedCoordShift_mem_omegaCoordSub_of_mem_local {m : ℕ} (hm : 0 < m)
    {B : Set E} (h0 : (0 : E) ∈ B) (u : ℤˣ) {w : FreeGroup ↥K}
    (hw : w ∈ localCoordSub m B) :
    signedCoordShift m u w ∈ omegaCoordSub m B := by
  apply signedCoordShift_mem_omegaCoordSub u
  exact localCoordSub_le_omegaCoordSub hm h0 hw

/-- **Classifier-to-scan seam.**  A pinched entry from the original inner
alphabet has a conjugate-basis spelling whose signed collapse already lies
in the global outer invariant. -/
theorem exists_global_shifted_cbWord_of_mem_slimWBase_toSubgroup
    {m : ℕ} (hm : 0 < m) {B : Set E} (h0 : (0 : E) ∈ B)
    {u : ℤˣ} {g : SlimPi m} (hgW : g ∈ slimWBase m B)
    (hgA : g ∈ HNNExtension.toSubgroup
      (slimPiF3Hom m).range (slimPiF3Hom m).range u) :
    ∃ (x : F₃) (w : FreeGroup ↥K),
      slimPiF3Hom m x = g ∧ cbHom w = x ∧
        signedCoordShift m u w ∈ omegaCoordSub m B := by
  obtain ⟨x, w, hx, hw, hwx⟩ :=
    exists_local_cbWord_of_mem_slimWBase_toSubgroup hgW hgA
  exact ⟨x, w, hx, hwx,
    signedCoordShift_mem_omegaCoordSub_of_mem_local hm h0 u hw⟩

end Omega
end Higman
end GroupApproximation
