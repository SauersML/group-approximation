import GroupApproximation.GGT.HullYiOrientationFreshening
import GroupApproximation.GGT.HullYiOrientationRadical

/-!
# Pairwise orientation-pure radical detectors

Hull's proof of Lemma 5.6 requires a finite orientation-pure family whose
elementary closures have trivial total intersection and whose members are
pairwise non-commensurable.  The radical detector supplies the first property.
The freshening theorem replaces its members one at a time while avoiding the
classes already selected.

Finite-order membership in each replacement implies membership in the
corresponding original closure.  Since two selected non-commensurable
loxodromics have finite elementary-closure intersection, this implication
transfers the original trivial-intersection property to the pairwise family.

The induction is finite and keeps the original index set.  Thus no reindexing
or cardinal comparison is needed by the cyclic-product consumer.
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

/-- Freshen every member of a finite orientation-pure family while retaining
finite-order membership in its corresponding original elementary closure. -/
theorem exists_pairwise_freshening_of_orientationPure_family_of_dgoLemma421b
    (h421b : DGOLemma421b.{u, 0}) (A : HullGeneratingSet G)
    {S : Subgroup G} (hS : ActsNonElementarily S (Cayley.base A.alphabet)) :
    ∀ {k : ℕ} (f : Fin k → G) (r : Fin k → ℕ),
      (∀ i, f i ∈ S) →
      (∀ i, IsLoxodromic (f i) (Cayley.base A.alphabet)) →
      (∀ i, 0 < r i) →
      (∀ i, (elementaryClosure (f i) : Set G) =
        {x : G | Commute x (f i ^ (r i : ℤ))}) →
      ∃ (g : Fin k → G) (s : Fin k → ℕ),
        (∀ i, g i ∈ S) ∧
        (∀ i, IsLoxodromic (g i) (Cayley.base A.alphabet)) ∧
        PairwiseNonCommensurable g ∧
        (∀ i, 0 < s i) ∧
        (∀ i, (elementaryClosure (g i) : Set G) =
          {x : G | Commute x (g i ^ (s i : ℤ))}) ∧
        ∀ i (x : G), IsOfFinOrder x → x ∈ elementaryClosure (g i) →
          x ∈ elementaryClosure (f i) := by
  classical
  intro k
  induction k with
  | zero =>
      intro f r hfS hflox hr hcentral
      refine ⟨Fin.elim0, Fin.elim0, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact fun i ↦ Fin.elim0 i
      · exact fun i ↦ Fin.elim0 i
      · exact pairwiseNonCommensurable_of_subsingleton Fin.elim0
      · exact fun i ↦ Fin.elim0 i
      · exact fun i ↦ Fin.elim0 i
      · exact fun i ↦ Fin.elim0 i
  | succ k ih =>
      intro f r hfS hflox hr hcentral
      let f0 : Fin k → G := fun i ↦ f i.castSucc
      let r0 : Fin k → ℕ := fun i ↦ r i.castSucc
      obtain ⟨old, oldR, holdS, holdLox, holdNc, holdRpos,
          holdCentral, holdFiniteIn⟩ :=
        ih f0 r0 (fun i ↦ hfS i.castSucc) (fun i ↦ hflox i.castSucc)
          (fun i ↦ hr i.castSucc) (fun i ↦ hcentral i.castSucc)
      let F : Finset G := Finset.univ.image old
      obtain ⟨fresh, freshR, hfreshS, hfreshLox, hfreshRpos,
          hfreshCentral, hfreshAvoid, hfreshFiniteIn⟩ :=
        exists_fresh_orientationPure_of_dgoLemma421b
          h421b A hS (hfS (Fin.last k)) (hflox (Fin.last k))
            (hr (Fin.last k)) (hcentral (Fin.last k)) F
      let g : Fin (k + 1) → G := Fin.snoc old fresh
      let s : Fin (k + 1) → ℕ := Fin.snoc oldR freshR
      have hgS : ∀ i, g i ∈ S := by
        intro i
        refine Fin.lastCases ?_ ?_ i
        · simpa [g, Fin.snoc_last] using hfreshS
        · intro j
          simpa [g, Fin.snoc_castSucc] using holdS j
      have hgLox : ∀ i,
          IsLoxodromic (g i) (Cayley.base A.alphabet) := by
        intro i
        refine Fin.lastCases ?_ ?_ i
        · simpa [g, Fin.snoc_last] using hfreshLox
        · intro j
          simpa [g, Fin.snoc_castSucc] using holdLox j
      have hgNc : PairwiseNonCommensurable g := by
        intro i
        refine Fin.lastCases ?_ ?_ i
        · intro j
          refine Fin.lastCases ?_ ?_ j
          · intro hij
            exact (hij rfl).elim
          · intro j0 hij p q hp hq t heq
            have hjF : old j0 ∈ F := by
              exact Finset.mem_image.mpr ⟨j0, Finset.mem_univ _, rfl⟩
            apply (hfreshAvoid (old j0) hjF).1
            refine ⟨p, q, t, hp, hq, ?_⟩
            simpa [g, Fin.snoc_last, Fin.snoc_castSucc] using heq
        · intro i0 j
          refine Fin.lastCases ?_ ?_ j
          · intro hij p q hp hq t heq
            have hiF : old i0 ∈ F := by
              exact Finset.mem_image.mpr ⟨i0, Finset.mem_univ _, rfl⟩
            apply (hfreshAvoid (old i0) hiF).2
            refine ⟨p, q, t, hp, hq, ?_⟩
            simpa [g, Fin.snoc_last, Fin.snoc_castSucc] using heq
          · intro j0 hij p q hp hq t heq
            have hij0 : i0 ≠ j0 := by
              intro hbad
              apply hij
              simp [hbad]
            exact holdNc i0 j0 hij0 p q hp hq t
              (by simpa [g, Fin.snoc_castSucc] using heq)
      have hsPos : ∀ i, 0 < s i := by
        intro i
        refine Fin.lastCases ?_ ?_ i
        · simpa [s, Fin.snoc_last] using hfreshRpos
        · intro j
          simpa [s, Fin.snoc_castSucc] using holdRpos j
      have hgCentral : ∀ i, (elementaryClosure (g i) : Set G) =
          {x : G | Commute x (g i ^ (s i : ℤ))} := by
        intro i
        refine Fin.lastCases ?_ ?_ i
        · simpa [g, s, Fin.snoc_last] using hfreshCentral
        · intro j
          simpa [g, s, Fin.snoc_castSucc] using holdCentral j
      refine ⟨g, s, hgS, hgLox, hgNc, hsPos, hgCentral, ?_⟩
      intro i
      refine Fin.lastCases ?_ ?_ i
      · intro x hxfinite hxmem
        apply hfreshFiniteIn x hxfinite
        simpa [g, Fin.snoc_last] using hxmem
      · intro j x hxfinite hxmem
        apply holdFiniteIn j x hxfinite
        simpa [g, Fin.snoc_castSucc] using hxmem

/-- **Hull's pairwise orientation-pure finite detector.**

For a suitable subgroup the total elementary-closure intersection is trivial,
and the family has at least three members as required by the cyclic product
argument. -/
theorem exists_fin_orientationPure_pairwise_family_trivial_intersection_of_dgoLemma421b
    (h421b : DGOLemma421b.{u, 0}) (A : HullGeneratingSet G)
    {S : Subgroup G} (hS : Suitable A.alphabet S) :
    ∃ (k : ℕ) (f : Fin k → G) (r : Fin k → ℕ), 3 ≤ k ∧
      (∀ i, f i ∈ S) ∧
      (∀ i, IsLoxodromic (f i) (Cayley.base A.alphabet)) ∧
      PairwiseNonCommensurable f ∧
      (∀ i, 0 < r i) ∧
      (∀ i, (elementaryClosure (f i) : Set G) =
        {x : G | Commute x (f i ^ (r i : ℤ))}) ∧
      ∀ x : G, (∀ i, x ∈ elementaryClosure (f i)) → x = 1 := by
  obtain ⟨k, raw, rawR, hk, hrawS, hrawLox, hrawRpos,
      hrawCentral, hrawInter⟩ :=
    exists_fin_orientationPure_family_trivial_intersection_of_dgoLemma421b
      h421b A hS
  obtain ⟨f, r, hfS, hflox, hfnc, hr, hcentral, hfiniteIn⟩ :=
    exists_pairwise_freshening_of_orientationPure_family_of_dgoLemma421b
      h421b A hS.actsNonElementarily raw rawR hrawS hrawLox
        hrawRpos hrawCentral
  let i0 : Fin k := ⟨0, by omega⟩
  let i1 : Fin k := ⟨1, by omega⟩
  have hIfin : ((elementaryClosure (f i0) ⊓
      elementaryClosure (f i1) : Subgroup G) : Set G).Finite := by
    have hind : Independent (f i0) (f i1) (Cayley.base A.alphabet) := by
      apply ElementaryMorse.independentOfNoCommonZpow_cayley A
        (f i0) (f i1) (hflox i0) (hflox i1)
      intro p q hp hq heq
      exact hfnc i0 i1 (by
        intro heqIndex
        have := congrArg Fin.val heqIndex
        simp [i0, i1] at this) p q hp hq 1 (by simpa using heq)
    by_contra hinfinite
    exact not_infinite_le_inf_elementaryClosure
      (isIsometricAction_cayley A.alphabet)
      (elementaryClosureVirtuallyCyclic_hullGeneratingSet A)
      (hflox i0) (hflox i1) hind inf_le_left inf_le_right hinfinite
  refine ⟨k, f, r, hk, hfS, hflox, hfnc, hr, hcentral, ?_⟩
  intro x hx
  have hxfinite : IsOfFinOrder x := by
    let I : Subgroup G := elementaryClosure (f i0) ⊓ elementaryClosure (f i1)
    let y : I := ⟨x, hx i0, hx i1⟩
    have hI : (I : Set G).Finite := hIfin
    letI : Finite I := hI.to_subtype
    exact Submonoid.isOfFinOrder_coe.mpr (isOfFinOrder_of_finite y)
  apply hrawInter x
  intro i
  exact hfiniteIn i x hxfinite (hx i)

end HullSC
end GroupApproximation
