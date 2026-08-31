import GroupApproximation.GGT.HullSCPublishedSmallCancellation
import GroupApproximation.GroupTheory.NormalClosureProduct

/-!
# The first diagram reduction in Hull's Lemma 4.4

The nonempty-relator branch of Hull's Lemma 4.4 starts with a relative van
Kampen diagram whose boundary is short and nontrivial.  This file proves the
exact algebraic reduction which produces that boundary.  If the natural
relator quotient is not injective on the radius-`R` ball, two words in that
ball have the same image.  Their difference is a nonidentity kernel element
of word length at most `2 * R`; equality of the kernel with the relator normal
closure supplies a finite relator-product certificate, i.e. the algebraic
2-cell data for a diagram.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.WordMetric

universe u w

/-- A short nontrivial boundary word together with a finite certificate that
it is filled by conjugates of members of the relative relator family. -/
structure Lemma44RelatorDiagramBoundary {G : Type u} [Group G]
    {Λ : Type w} (A : Alphabet G)
    (W : Set (List (GGT.RelLetter G Λ))) (R : ℕ) where
  boundary : G
  boundary_ne_one : boundary ≠ 1
  boundary_length_le : wordNorm A.carrier boundary ≤ 2 * R
  area : ℕ
  area_pos : 0 < area
  isRelatorProduct : RelatorDefectBudget.IsRelatorProduct
    (GGT.RelLetter.listVal '' W) area boundary
  area_minimal : ∀ {m : ℕ}, RelatorDefectBudget.IsRelatorProduct
    (GGT.RelLetter.listVal '' W) m boundary → area ≤ m

/-- Failure of injectivity on the radius-`R` ball produces the short
nontrivial relator diagram with which the proof of Hull's Lemma 4.4 begins. -/
theorem exists_lemma44RelatorDiagramBoundary_of_not_injOn
    {G : Type u} [Group G] {Λ : Type w} (A : Alphabet G)
    (W : Set (List (GGT.RelLetter G Λ))) (R : ℕ)
    {Q : Type*} [Group Q] (q : G →* Q)
    (hker : q.ker = Subgroup.normalClosure (GGT.RelLetter.listVal '' W))
    (hnot : ¬ Set.InjOn q (cayleyBall A R)) :
    Nonempty (Lemma44RelatorDiagramBoundary A W R) := by
  classical
  simp only [Set.InjOn] at hnot
  push Not at hnot
  obtain ⟨x, hx, y, hy, hxy, hne⟩ := hnot
  let z := x⁻¹ * y
  have hz_ne : z ≠ 1 := by
    intro hz
    exact hne (inv_mul_eq_one.mp hz)
  have hz_ker : z ∈ q.ker := by
    apply MonoidHom.mem_ker.mpr
    dsimp [z]
    rw [map_mul, map_inv, hxy]
    simp
  have hx_len : wordNorm A.carrier x ≤ R := by
    have hx' := (mem_cayleyBall_iff A R x).mp hx
    rwa [wordDist_one_left] at hx'
  have hy_len : wordNorm A.carrier y ≤ R := by
    have hy' := (mem_cayleyBall_iff A R y).mp hy
    rwa [wordDist_one_left] at hy'
  have hz_len : wordNorm A.carrier z ≤ 2 * R := by
    have hmul := wordNorm_mul_le A.symmetricGenerating x⁻¹ y
    rw [wordNorm_inv A.symmetricGenerating x] at hmul
    dsimp [z]
    omega
  have hz_normal : z ∈
      Subgroup.normalClosure (GGT.RelLetter.listVal '' W) := by
    rw [← hker]
    exact hz_ker
  have hex : ∃ area, RelatorDefectBudget.IsRelatorProduct
      (GGT.RelLetter.listVal '' W) area z :=
    RelatorDefectBudget.exists_isRelatorProduct hz_normal
  let area := Nat.find hex
  have harea : RelatorDefectBudget.IsRelatorProduct
      (GGT.RelLetter.listVal '' W) area z := Nat.find_spec hex
  have harea_pos : 0 < area := by
    apply Nat.pos_of_ne_zero
    intro hzero
    have harea0 : RelatorDefectBudget.IsRelatorProduct
        (GGT.RelLetter.listVal '' W) 0 z := by
      simpa [hzero] using harea
    exact hz_ne harea0.eq_one_of_index_zero
  exact ⟨{
    boundary := z
    boundary_ne_one := hz_ne
    boundary_length_le := hz_len
    area := area
    area_pos := harea_pos
    isRelatorProduct := harea
    area_minimal := fun h => Nat.find_min' hex h
  }⟩

end HullSC
end GroupApproximation
