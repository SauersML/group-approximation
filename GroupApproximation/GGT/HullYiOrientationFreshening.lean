import GroupApproximation.GGT.HullYiOrientationProductTriple
import GroupApproximation.GGT.HullYiFiniteFamilyInduction

/-!
# Fresh orientation-pure detector classes

Hull's selection of a finite pairwise non-commensurable detector can be made
inductively.  Given one orientation-pure detector, finite counting first
chooses two more orientation-pure classes which avoid it.  The prescribed-
triple product theorem then supplies enough new classes to avoid any finite
list already selected.

For finite-order elements, membership in the new elementary closure implies
membership in the original detector elementary closure.  This is the
invariant used to retain the trivial total intersection during the induction.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.GGT
open GroupApproximation.GGT.Elementary
open GroupApproximation.GGT.OsinComponents
open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

variable {G : Type u} [Group G]

/-- One orientation-pure detector can be replaced by a fresh class avoiding a
prescribed finite set.  Finite-order membership in the new elementary closure
still implies membership in the original elementary closure. -/
theorem exists_fresh_orientationPure_of_dgoLemma421b
    (h421b : DGOLemma421b.{u, 0}) (A : HullGeneratingSet G)
    {S : Subgroup G} (hS : ActsNonElementarily S (Cayley.base A.alphabet))
    {h : G} (hhS : h ∈ S)
    (hhlox : IsLoxodromic h (Cayley.base A.alphabet))
    {rh : ℕ} (hrh : 0 < rh)
    (hhcentral : (elementaryClosure h : Set G) =
      {x : G | Commute x (h ^ (rh : ℤ))})
    (F : Finset G) :
    ∃ (g : G) (s : ℕ), g ∈ S ∧
      IsLoxodromic g (Cayley.base A.alphabet) ∧
      0 < s ∧
      (elementaryClosure g : Set G) =
        {x : G | Commute x (g ^ (s : ℤ))} ∧
      AvoidsFiniteCommensurability F g ∧
      ∀ x : G, IsOfFinOrder x → x ∈ elementaryClosure g →
        x ∈ elementaryClosure h := by
  classical
  let H : Finset G := {h}
  obtain ⟨base, baseR, hbaseS, hbaseLox, hbaseNc, -, hbaseRpos,
      hbaseCentral⟩ :=
    exists_orientationPure_family_of_dgoLemma421b
      h421b A hS (H.card + 2)
  obtain ⟨i, j, hij, hiAvoid, hjAvoid⟩ :=
    finiteCommensurabilityAvoidance H base hbaseNc
  let q : Fin 3 → G := ![h, base i, base j]
  let r : Fin 3 → ℕ := ![rh, baseR i, baseR j]
  have hqS : ∀ z, q z ∈ S := by
    intro z
    fin_cases z
    · exact hhS
    · exact hbaseS i
    · exact hbaseS j
  have hqlox : ∀ z,
      IsLoxodromic (q z) (Cayley.base A.alphabet) := by
    intro z
    fin_cases z
    · exact hhlox
    · exact hbaseLox i
    · exact hbaseLox j
  have hqnc : PairwiseNonCommensurable q := by
    intro z w hzw p v hp hv t
    fin_cases z <;> fin_cases w
    · exact (hzw rfl).elim
    · intro heq
      exact (hiAvoid h (by simp [H])).2 ⟨p, v, t, hp, hv, heq⟩
    · intro heq
      exact (hjAvoid h (by simp [H])).2 ⟨p, v, t, hp, hv, heq⟩
    · intro heq
      exact (hiAvoid h (by simp [H])).1 ⟨p, v, t, hp, hv, heq⟩
    · exact (hzw rfl).elim
    · exact hbaseNc i j hij p v hp hv t
    · intro heq
      exact (hjAvoid h (by simp [H])).1 ⟨p, v, t, hp, hv, heq⟩
    · exact hbaseNc j i hij.symm p v hp hv t
    · exact (hzw rfl).elim
  have hr : ∀ z, 0 < r z := by
    intro z
    fin_cases z
    · exact hrh
    · exact hbaseRpos i
    · exact hbaseRpos j
  have hcentral : ∀ z, (elementaryClosure (q z) : Set G) =
      {x : G | Commute x (q z ^ (r z : ℤ))} := by
    intro z
    fin_cases z
    · exact hhcentral
    · exact hbaseCentral i
    · exact hbaseCentral j
  obtain ⟨candidate, candidateR, hcS, hclox, hcnc, hcRpos,
      hcCentral, hcFiniteIn⟩ :=
    exists_orientationPure_products_of_triple_of_dgoLemma421b
      h421b A q r hqS hqlox hqnc hr hcentral (F.card + 2)
  obtain ⟨m, _n, _hmn, hmAvoid, _hnAvoid⟩ :=
    finiteCommensurabilityAvoidance F candidate hcnc
  refine ⟨candidate m, candidateR m, hcS m, hclox m, hcRpos m,
    hcCentral m, hmAvoid, ?_⟩
  intro x hxfinite hxmem
  exact hcFiniteIn m x hxfinite hxmem 0

end HullSC
end GroupApproximation
