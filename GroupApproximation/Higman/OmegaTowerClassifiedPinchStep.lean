import GroupApproximation.Higman.OmegaTowerConjugateBasisPinchRewrite
import GroupApproximation.Higman.OmegaTowerLocalGlobalCoordinates

/-!
# One classified step of the outer Omega scan

This combines the inner matched-word classifier, the signed edge action, and
the exact two-letter product collapse.  The output both shortens the displayed
outer pinch and records that the new conjugate-basis word lies in the global
coordinate invariant.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open Conj Seq HNNExtension

/-- **Classified outer pinch step.**  A pinched entry from `slimWBase` is
replaced by its exact signed coordinate shift; that shifted word lies in the
global invariant used by the continuing scan. -/
theorem exists_classified_outer_pinch_step
    {m : ℕ} (hm : 0 < m) {B : Set E} (h0 : (0 : E) ∈ B)
    (u : ℤˣ) {g : SlimPi m} (hgW : g ∈ slimWBase m B)
    (hgA : g ∈ toSubgroup
      (slimPiF3Hom m).range (slimPiF3Hom m).range u)
    (g' : SlimPi m) (tail : List (ℤˣ × SlimPi m)) :
    ∃ w : FreeGroup ↥K,
      signedCoordShift m u w ∈ omegaCoordSub m B ∧
      ((((u, g) :: (-u, g') :: tail).map
          (HNNDescent.letter (slimShiftRangeEquiv m))).prod) =
        of (slimPiF3Hom m (cbHom (signedCoordShift m u w)) * g') *
          ((tail.map (HNNDescent.letter (slimShiftRangeEquiv m))).prod) := by
  obtain ⟨x, w, hx, hwx, hwglobal⟩ :=
    exists_global_shifted_cbWord_of_mem_slimWBase_toSubgroup
      hm h0 hgW hgA
  refine ⟨w, hwglobal, ?_⟩
  have hgw : g = slimPiF3Hom m (cbHom w) :=
    hx.symm.trans (congrArg (slimPiF3Hom m) hwx.symm)
  rw [hgw]
  exact prod_outer_cbHom_pair m u w g' tail

/-- The same classified collapse at the level of a complete outer word.  The
new spelling has exactly two fewer stable letters, and the coordinate word
created by the collapse remains available as an explicit invariant witness. -/
theorem exists_shorter_classified_outer_gword
    {m : ℕ} (hm : 0 < m) {B : Set E} (h0 : (0 : E) ∈ B)
    (z₀ : SlimPi m) (l₁ : List (ℤˣ × SlimPi m)) (u : ℤˣ)
    {g : SlimPi m} (hgW : g ∈ slimWBase m B)
    (hgA : g ∈ toSubgroup
      (slimPiF3Hom m).range (slimPiF3Hom m).range u)
    (g' : SlimPi m) (l₂ : List (ℤˣ × SlimPi m)) :
    ∃ (w : FreeGroup ↥K) (z₀' : SlimPi m)
        (l' : List (ℤˣ × SlimPi m)),
      signedCoordShift m u w ∈ omegaCoordSub m B ∧
      HNNDescent.gword (slimShiftRangeEquiv m) z₀
          (l₁ ++ (u, g) :: (-u, g') :: l₂) =
        HNNDescent.gword (slimShiftRangeEquiv m) z₀' l' ∧
      l'.length + 2 = (l₁ ++ (u, g) :: (-u, g') :: l₂).length := by
  obtain ⟨w, hwglobal, hprod⟩ :=
    exists_classified_outer_pinch_step hm h0 u hgW hgA g' l₂
  let y : SlimPi m :=
    slimPiF3Hom m (cbHom (signedCoordShift m u w))
  rcases HNNDescent.eq_nil_or_append_singleton l₁ with
    rfl | ⟨l₁', c, rfl⟩
  · refine ⟨w, z₀ * (y * g'), l₂, hwglobal, ?_, by simp⟩
    simp only [List.nil_append, HNNDescent.gword]
    rw [hprod, ← mul_assoc, ← map_mul]
  · obtain ⟨v, w₀⟩ := c
    refine ⟨w, z₀, l₁' ++ (v, w₀ * (y * g')) :: l₂,
      hwglobal, ?_, ?_⟩
    · have hlist :
          l₁' ++ [(v, w₀)] ++ (u, g) :: (-u, g') :: l₂ =
            l₁' ++ ((v, w₀) :: (u, g) :: (-u, g') :: l₂) := by
          simp
      rw [hlist]
      apply HNNDescent.gword_append_eq (slimShiftRangeEquiv m) z₀ l₁'
      rw [List.map_cons, List.prod_cons, hprod, ← mul_assoc,
        HNNDescent.letter_mul_of (slimShiftRangeEquiv m) v w₀ (y * g'),
        List.map_cons, List.prod_cons]
    · simp only [List.length_append, List.length_cons, List.length_nil]
      omega

end Omega
end Higman
end GroupApproximation
