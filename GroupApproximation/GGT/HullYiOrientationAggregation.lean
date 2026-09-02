import GroupApproximation.GGT.HullYiOrientationPairwiseDetector

/-!
# Aggregating a finite orientation-pure detector into a triple

Hull's cyclic-product construction may use any finite detector of size at
least three.  The landed fixed-side separation theorem is already strongest
at three letters, so this module reduces the detector to that case without
changing its finite intersection.

The induction aggregates one detector at a time.  Its state is an
orientation-pure loxodromic `h` such that every finite-order member of `E(h)`
belongs to each elementary closure already processed.  Before adding the next
detector, `h` is selected to avoid its commensurability class.  A third fresh
class completes a pairwise triple, and the prescribed-triple product theorem
produces the next aggregate.

After all detectors are processed, two further freshenings give an exact
three-member pairwise orientation-pure family.  Membership in the first two
closures is finite, so the aggregate invariant transfers it into the original
trivial intersection.
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

/-- Aggregate a finite orientation-pure family into one fresh
orientation-pure class.  Finite-order membership in the aggregate closure
implies membership in every input closure. -/
theorem exists_orientationPure_aggregate_of_dgoLemma421b
    (h421b : DGOLemma421b.{u, 0}) (A : HullGeneratingSet G)
    {S : Subgroup G} (hS : ActsNonElementarily S (Cayley.base A.alphabet)) :
    ∀ {k : ℕ} (f : Fin k → G) (r : Fin k → ℕ),
      (∀ i, f i ∈ S) →
      (∀ i, IsLoxodromic (f i) (Cayley.base A.alphabet)) →
      (∀ i, 0 < r i) →
      (∀ i, (elementaryClosure (f i) : Set G) =
        {x : G | Commute x (f i ^ (r i : ℤ))}) →
      ∀ F : Finset G,
      ∃ (h : G) (s : ℕ), h ∈ S ∧
        IsLoxodromic h (Cayley.base A.alphabet) ∧
        0 < s ∧
        (elementaryClosure h : Set G) =
          {x : G | Commute x (h ^ (s : ℤ))} ∧
        AvoidsFiniteCommensurability F h ∧
        ∀ x : G, IsOfFinOrder x → x ∈ elementaryClosure h →
          ∀ i, x ∈ elementaryClosure (f i) := by
  classical
  intro k
  induction k with
  | zero =>
      intro f r hfS hflox hr hcentral F
      obtain ⟨candidate, candidateR, hcS, hcLox, hcNc, -, hcRpos,
          hcCentral⟩ :=
        exists_orientationPure_family_of_dgoLemma421b
          h421b A hS (F.card + 2)
      obtain ⟨i, _j, _hij, hiAvoid, _hjAvoid⟩ :=
        finiteCommensurabilityAvoidance F candidate hcNc
      refine ⟨candidate i, candidateR i, hcS i, hcLox i, hcRpos i,
        hcCentral i, hiAvoid, ?_⟩
      intro x hxfinite hxmem z
      exact Fin.elim0 z
  | succ k ih =>
      intro f r hfS hflox hr hcentral F
      let f0 : Fin k → G := fun i ↦ f i.castSucc
      let r0 : Fin k → ℕ := fun i ↦ r i.castSucc
      let Fnext : Finset G := insert (f (Fin.last k)) F
      obtain ⟨old, oldR, holdS, holdLox, holdRpos, holdCentral,
          holdAvoid, holdFiniteIn⟩ :=
        ih f0 r0 (fun i ↦ hfS i.castSucc) (fun i ↦ hflox i.castSucc)
          (fun i ↦ hr i.castSucc) (fun i ↦ hcentral i.castSucc) Fnext
      let Q : Finset G := {old, f (Fin.last k)}
      obtain ⟨fresh, freshR, hfreshS, hfreshLox, hfreshRpos,
          hfreshCentral, hfreshAvoid, _hfreshFiniteIn⟩ :=
        exists_fresh_orientationPure_of_dgoLemma421b
          h421b A hS holdS holdLox holdRpos holdCentral Q
      let q : Fin 3 → G := ![old, f (Fin.last k), fresh]
      let qr : Fin 3 → ℕ := ![oldR, r (Fin.last k), freshR]
      have hqS : ∀ i, q i ∈ S := by
        intro i
        fin_cases i
        · exact holdS
        · exact hfS (Fin.last k)
        · exact hfreshS
      have hqLox : ∀ i,
          IsLoxodromic (q i) (Cayley.base A.alphabet) := by
        intro i
        fin_cases i
        · exact holdLox
        · exact hflox (Fin.last k)
        · exact hfreshLox
      have hqNc : PairwiseNonCommensurable q := by
        intro i j hij p z hp hz t
        fin_cases i <;> fin_cases j
        · exact (hij rfl).elim
        · intro heq
          exact (holdAvoid (f (Fin.last k)) (by simp [Fnext])).1
            ⟨p, z, t, hp, hz, heq⟩
        · intro heq
          exact (hfreshAvoid old (by simp [Q])).2
            ⟨p, z, t, hp, hz, heq⟩
        · intro heq
          exact (holdAvoid (f (Fin.last k)) (by simp [Fnext])).2
            ⟨p, z, t, hp, hz, heq⟩
        · exact (hij rfl).elim
        · intro heq
          exact (hfreshAvoid (f (Fin.last k)) (by simp [Q])).2
            ⟨p, z, t, hp, hz, heq⟩
        · intro heq
          exact (hfreshAvoid old (by simp [Q])).1
            ⟨p, z, t, hp, hz, heq⟩
        · intro heq
          exact (hfreshAvoid (f (Fin.last k)) (by simp [Q])).1
            ⟨p, z, t, hp, hz, heq⟩
        · exact (hij rfl).elim
      have hqrPos : ∀ i, 0 < qr i := by
        intro i
        fin_cases i
        · exact holdRpos
        · exact hr (Fin.last k)
        · exact hfreshRpos
      have hqCentral : ∀ i, (elementaryClosure (q i) : Set G) =
          {x : G | Commute x (q i ^ (qr i : ℤ))} := by
        intro i
        fin_cases i
        · exact holdCentral
        · exact hcentral (Fin.last k)
        · exact hfreshCentral
      obtain ⟨candidate, candidateR, hcS, hcLox, hcNc, hcRpos,
          hcCentral, hcFiniteIn⟩ :=
        exists_orientationPure_products_of_triple_of_dgoLemma421b
          h421b A q qr hqS hqLox hqNc hqrPos hqCentral (F.card + 2)
      obtain ⟨m, _n, _hmn, hmAvoid, _hnAvoid⟩ :=
        finiteCommensurabilityAvoidance F candidate hcNc
      refine ⟨candidate m, candidateR m, hcS m, hcLox m, hcRpos m,
        hcCentral m, hmAvoid, ?_⟩
      intro x hxfinite hxmem i
      have hxq := hcFiniteIn m x hxfinite hxmem
      refine Fin.lastCases ?_ ?_ i
      · exact hxq 1
      · intro i0
        exact holdFiniteIn x hxfinite (hxq 0) i0

/-- **Hull's orientation-pure detector triple.**

The three members are pairwise non-commensurable, their elementary closures
have trivial total intersection, and each has the centralizer power required
by the cyclic-product construction. -/
theorem exists_orientationPure_triple_trivial_intersection_of_dgoLemma421b
    (h421b : DGOLemma421b.{u, 0}) (A : HullGeneratingSet G)
    {S : Subgroup G} (hS : Suitable A.alphabet S) :
    ∃ (f : Fin 3 → G) (r : Fin 3 → ℕ),
      (∀ i, f i ∈ S) ∧
      (∀ i, IsLoxodromic (f i) (Cayley.base A.alphabet)) ∧
      PairwiseNonCommensurable f ∧
      (∀ i, 0 < r i) ∧
      (∀ i, (elementaryClosure (f i) : Set G) =
        {x : G | Commute x (f i ^ (r i : ℤ))}) ∧
      ∀ x : G, (∀ i, x ∈ elementaryClosure (f i)) → x = 1 := by
  classical
  obtain ⟨k, raw, rawR, _hk, hrawS, hrawLox, _hrawNc,
      hrawRpos, hrawCentral, hrawInter⟩ :=
    exists_fin_orientationPure_pairwise_family_trivial_intersection_of_dgoLemma421b
      h421b A hS
  obtain ⟨h, rh, hhS, hhLox, hrh, hhCentral, _hhAvoid, hhFiniteIn⟩ :=
    exists_orientationPure_aggregate_of_dgoLemma421b
      h421b A hS.actsNonElementarily raw rawR hrawS hrawLox
        hrawRpos hrawCentral ∅
  let H : Finset G := {h}
  obtain ⟨g, rg, hgS, hgLox, hrg, hgCentral, hgAvoid, _hgFiniteIn⟩ :=
    exists_fresh_orientationPure_of_dgoLemma421b
      h421b A hS.actsNonElementarily hhS hhLox hrh hhCentral H
  let K : Finset G := {h, g}
  obtain ⟨z, rz, hzS, hzLox, hrz, hzCentral, hzAvoid, _hzFiniteIn⟩ :=
    exists_fresh_orientationPure_of_dgoLemma421b
      h421b A hS.actsNonElementarily hhS hhLox hrh hhCentral K
  let f : Fin 3 → G := ![h, g, z]
  let r : Fin 3 → ℕ := ![rh, rg, rz]
  have hfS : ∀ i, f i ∈ S := by
    intro i
    fin_cases i
    · exact hhS
    · exact hgS
    · exact hzS
  have hfLox : ∀ i,
      IsLoxodromic (f i) (Cayley.base A.alphabet) := by
    intro i
    fin_cases i
    · exact hhLox
    · exact hgLox
    · exact hzLox
  have hfNc : PairwiseNonCommensurable f := by
    intro i j hij p q hp hq t
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · intro heq
      exact (hgAvoid h (by simp [H])).2 ⟨p, q, t, hp, hq, heq⟩
    · intro heq
      exact (hzAvoid h (by simp [K])).2 ⟨p, q, t, hp, hq, heq⟩
    · intro heq
      exact (hgAvoid h (by simp [H])).1 ⟨p, q, t, hp, hq, heq⟩
    · exact (hij rfl).elim
    · intro heq
      exact (hzAvoid g (by simp [K])).2 ⟨p, q, t, hp, hq, heq⟩
    · intro heq
      exact (hzAvoid h (by simp [K])).1 ⟨p, q, t, hp, hq, heq⟩
    · intro heq
      exact (hzAvoid g (by simp [K])).1 ⟨p, q, t, hp, hq, heq⟩
    · exact (hij rfl).elim
  have hrPos : ∀ i, 0 < r i := by
    intro i
    fin_cases i
    · exact hrh
    · exact hrg
    · exact hrz
  have hfCentral : ∀ i, (elementaryClosure (f i) : Set G) =
      {x : G | Commute x (f i ^ (r i : ℤ))} := by
    intro i
    fin_cases i
    · exact hhCentral
    · exact hgCentral
    · exact hzCentral
  have hIfin : ((elementaryClosure h ⊓ elementaryClosure g : Subgroup G) :
      Set G).Finite := by
    have hind : Independent h g (Cayley.base A.alphabet) := by
      apply ElementaryMorse.independentOfNoCommonZpow_cayley A
        h g hhLox hgLox
      intro p q hp hq heq
      apply (hgAvoid h (by simp [H])).2
      exact ⟨p, q, 1, hp, hq, by simpa using heq⟩
    by_contra hinfinite
    exact not_infinite_le_inf_elementaryClosure
      (isIsometricAction_cayley A.alphabet)
      (elementaryClosureVirtuallyCyclic_hullGeneratingSet A)
      hhLox hgLox hind inf_le_left inf_le_right hinfinite
  refine ⟨f, r, hfS, hfLox, hfNc, hrPos, hfCentral, ?_⟩
  intro x hx
  have hxfinite : IsOfFinOrder x := by
    let I : Subgroup G := elementaryClosure h ⊓ elementaryClosure g
    let y : I := ⟨x, hx 0, hx 1⟩
    have hI : (I : Set G).Finite := hIfin
    letI : Finite I := hI.to_subtype
    exact Submonoid.isOfFinOrder_coe.mpr (isOfFinOrder_of_finite y)
  apply hrawInter x
  exact hhFiniteIn x hxfinite (hx 0)

end HullSC
end GroupApproximation
