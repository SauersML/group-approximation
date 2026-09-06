import GroupApproximation.CharClass.CohomologyLHDegreewise
import GroupApproximation.CharClass.RelativeLES

/-!
# Restriction to a subspace, one degree below the top

`cc-thom`'s pair argument needs the restriction `H^{2r-1}(P) → H^{2r-1}(Z)` to be
onto.  Under Leray–Hirsch that map is the identity on coefficients, and the reason
is an index computation worth stating before the proof.

At the odd degree `2r - 1` the two index sets have the **same** size:

```text
lhDomainCard (r+1) (2r-1) = r        lhDomainCard r (2r-1) = r
```

because `(2r-1)/2` is `r-1`, so the second factor of each `min` is `r`.  A summand
is dropped at the *even* degree `2r`, where the two cardinals are `r+1` and `r`.
So the restriction here is between families of equal size and is **bijective**;
surjectivity is the weaker half.  This matters for cost as well as for truth: the
index changes type but not value, so every transport is `rfl`.

The statement needs `1 ≤ r`.  At `r = 0` the degree `2r - 1` is truncated
subtraction and evaluates to `0`, where the two cardinals are `1` and `0` and no
map is onto.

The two maps relating the ambient and the subspace enter only through the two
equations the proof uses: that the inclusion followed by the projection is the
restricted projection, and that the class restricts to the class.  Neither is
constructed here, so the result holds of whatever supplies them.

## Main declarations

* `LHCast.lhDomainEquiv2`, `LHCast.lhMap_eq_sum_lhTerm2` — the index transport at
  an arbitrary target cardinal, generalising the equal-to-the-rank case.
* `LHCast.pull_lhTerm` — restriction carries a column term to a column term.
* `LHCast.lhDomainCard_two_mul_sub_one` — the index computation above.
* `LHCast.bijective_pull_of_graded` — **the restriction is bijective**.
* `LHCast.absToSub_surjective_of_graded` — the corollary in `cc-thom`'s shape.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

namespace LHCast

open LH

variable {X P : TopCat.{0}}

/-! ## 1. The transport at an arbitrary target cardinal -/

/-- The index equivalence when the cardinal is some `s`, not necessarily the rank.
`lhIndexEquiv` is the case `s = r`. -/
def lhIndexEquiv2 (R n s : ℕ) (h : lhDomainCard R n = s) :
    Fin (lhDomainCard R n) ≃ Fin s where
  toFun i := ⟨(i : ℕ), by rw [← h]; exact i.isLt⟩
  invFun i := ⟨(i : ℕ), by rw [h]; exact i.isLt⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The coefficient transport at an arbitrary target cardinal. -/
def lhDomainEquiv2 (X : TopCat.{0}) (R n s : ℕ) (h : lhDomainCard R n = s) :
    ((i : Fin (lhDomainCard R n)) → Hmod2 X (n - 2 * (i : ℕ)))
      ≃ₗ[ZMod 2] ((i : Fin s) → Hmod2 X (n - 2 * (i : ℕ))) where
  toFun a i := a ((lhIndexEquiv2 R n s h).symm i)
  invFun b i := b (lhIndexEquiv2 R n s h i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv a := by funext i; rfl
  right_inv b := by funext i; rfl

set_option maxHeartbeats 1000000 in
theorem lhMap_eq_sum_lhTerm2 (π : P ⟶ X) (ξ : Hmod2 P 2) (R n s : ℕ)
    (h : lhDomainCard R n = s)
    (a : (i : Fin (lhDomainCard R n)) → Hmod2 X (n - 2 * (i : ℕ))) :
    lhMap π ξ R n a
      = ∑ i : Fin s, lhTerm π ξ n (i : ℕ) (lhDomainEquiv2 X R n s h a i) := by
  simp only [lhMap]
  refine Fintype.sum_equiv (lhIndexEquiv2 R n s h) _ _ (fun i => ?_)
  exact (lhTerm_of_le π ξ (two_mul_le_of_lhDomain i) (a i)).symm

set_option maxHeartbeats 1000000 in
/-- The coefficient description at a degree whose cardinal is `s`. -/
theorem bijective_sum_lhTerm_of_card {π : P ⟶ X} {ξ : Hmod2 P 2} {R : ℕ}
    (L : LerayHirschGraded π ξ R) (n s : ℕ) (h : lhDomainCard R n = s) :
    Function.Bijective (fun a : (i : Fin s) → Hmod2 X (n - 2 * (i : ℕ)) =>
      ∑ i : Fin s, lhTerm π ξ n (i : ℕ) (a i)) := by
  have hfun : (fun a : (i : Fin s) → Hmod2 X (n - 2 * (i : ℕ)) =>
      ∑ i : Fin s, lhTerm π ξ n (i : ℕ) (a i))
      = (lhMap π ξ R n) ∘ (lhDomainEquiv2 X R n s h).symm := by
    funext a
    have hb := lhMap_eq_sum_lhTerm2 π ξ R n s h ((lhDomainEquiv2 X R n s h).symm a)
    rw [(lhDomainEquiv2 X R n s h).apply_symm_apply] at hb
    exact hb.symm
  rw [hfun]
  exact (L.bij n).comp (lhDomainEquiv2 X R n s h).symm.bijective

/-! ## 2. Restriction carries a column term to a column term -/

set_option maxHeartbeats 1000000 in
/-- **A column term restricts to the column term at the same index.**  Only the two
equations enter: the inclusion followed by the projection is the restricted
projection, and the class restricts to the class. -/
theorem pull_lhTerm {Q : TopCat.{0}} (f : Q ⟶ P) (π : P ⟶ X) (π' : Q ⟶ X)
    (hπ : f ≫ π = π') (ξ : Hmod2 P 2) (ξ' : Hmod2 Q 2) (hξ : pull f 2 ξ = ξ')
    (n i : ℕ) (a : Hmod2 X (n - 2 * i)) :
    pull f n (lhTerm π ξ n i a) = lhTerm π' ξ' n i a := by
  by_cases hi : 2 * i ≤ n
  · rw [lhTerm_of_le π ξ hi, lhTerm_of_le π' ξ' hi, KnHemi.pull_cohCast, pull_cup,
      ← pull_comp, hπ, pull_cupPowE, hξ]
  · rw [lhTerm_of_gt π ξ hi, lhTerm_of_gt π' ξ' hi, pull_zero]

/-! ## 3. The index computation -/

/-- At the odd degree `2r - 1` the rank-`(r+1)` index set has `r` elements. -/
theorem lhDomainCard_succ_two_mul_sub_one (r : ℕ) (hr : 1 ≤ r) :
    lhDomainCard (r + 1) (2 * r - 1) = r := by
  unfold lhDomainCard
  omega

/-- And so does the rank-`r` one, which is why the restriction is bijective here
rather than a projection. -/
theorem lhDomainCard_two_mul_sub_one (r : ℕ) (hr : 1 ≤ r) :
    lhDomainCard r (2 * r - 1) = r := by
  unfold lhDomainCard
  omega

/-! ## 4. The restriction is bijective -/

set_option maxHeartbeats 1000000 in
/-- **The restriction one degree below the top is bijective.**  Both index sets
have `r` elements there, and the restriction is the identity on coefficients. -/
theorem bijective_pull_of_graded {Q : TopCat.{0}} (f : Q ⟶ P)
    (π : P ⟶ X) (π' : Q ⟶ X) (hπ : f ≫ π = π')
    (ξ : Hmod2 P 2) (ξ' : Hmod2 Q 2) (hξ : pull f 2 ξ = ξ')
    (r : ℕ) (hr : 1 ≤ r)
    (L : LerayHirschGraded π ξ (r + 1)) (L' : LerayHirschGraded π' ξ' r) :
    Function.Bijective (pull f (2 * r - 1)) := by
  have hF : Function.Bijective
      (fun a : (i : Fin r) → Hmod2 X (2 * r - 1 - 2 * (i : ℕ)) =>
        ∑ i : Fin r, lhTerm π ξ (2 * r - 1) (i : ℕ) (a i)) :=
    bijective_sum_lhTerm_of_card L (2 * r - 1) r
      (lhDomainCard_succ_two_mul_sub_one r hr)
  have hG : Function.Bijective
      (fun a : (i : Fin r) → Hmod2 X (2 * r - 1 - 2 * (i : ℕ)) =>
        ∑ i : Fin r, lhTerm π' ξ' (2 * r - 1) (i : ℕ) (a i)) :=
    bijective_sum_lhTerm_of_card L' (2 * r - 1) r
      (lhDomainCard_two_mul_sub_one r hr)
  have hcomp : (pull f (2 * r - 1)) ∘
      (fun a : (i : Fin r) → Hmod2 X (2 * r - 1 - 2 * (i : ℕ)) =>
        ∑ i : Fin r, lhTerm π ξ (2 * r - 1) (i : ℕ) (a i))
      = fun a : (i : Fin r) → Hmod2 X (2 * r - 1 - 2 * (i : ℕ)) =>
        ∑ i : Fin r, lhTerm π' ξ' (2 * r - 1) (i : ℕ) (a i) := by
    funext a
    show pull f (2 * r - 1) (∑ i : Fin r, lhTerm π ξ (2 * r - 1) (i : ℕ) (a i)) = _
    have hsum : pull f (2 * r - 1)
        (∑ i : Fin r, lhTerm π ξ (2 * r - 1) (i : ℕ) (a i))
        = ∑ i : Fin r, pull f (2 * r - 1) (lhTerm π ξ (2 * r - 1) (i : ℕ) (a i)) :=
      map_sum (pullLinear f (2 * r - 1)) _ _
    rw [hsum]
    exact Finset.sum_congr rfl
      (fun i _ => pull_lhTerm f π π' hπ ξ ξ' hξ (2 * r - 1) (i : ℕ) (a i))
  have hGF : Function.Bijective ((pull f (2 * r - 1)) ∘
      (fun a : (i : Fin r) → Hmod2 X (2 * r - 1 - 2 * (i : ℕ)) =>
        ∑ i : Fin r, lhTerm π ξ (2 * r - 1) (i : ℕ) (a i))) := by
    rw [hcomp]
    exact hG
  exact (Function.Bijective.of_comp_iff (pull f (2 * r - 1)) hF).mp hGF

/-! ## 5. The corollary `cc-thom` consumes -/

/-- **`cc-thom`'s input.**  The restriction of the pair one degree below the top is
onto, which their `relToAbs_injective_of_absToSub_surjective` turns into
injectivity at the top. -/
theorem absToSub_surjective_of_graded (Z : Set P)
    (π : P ⟶ X) (π' : TopCat.of Z ⟶ X) (hπ : sInclusion Z ≫ π = π')
    (ξ : Hmod2 P 2) (ξ' : Hmod2 (TopCat.of Z) 2)
    (hξ : pull (sInclusion Z) 2 ξ = ξ')
    (r : ℕ) (hr : 1 ≤ r)
    (L : LerayHirschGraded π ξ (r + 1)) (L' : LerayHirschGraded π' ξ' r) :
    Function.Surjective (absToSub (ZMod 2) Z (2 * r - 1)).hom := by
  intro y
  obtain ⟨x, hx⟩ :=
    (bijective_pull_of_graded (sInclusion Z) π π' hπ ξ ξ' hξ r hr L L').2 y
  refine ⟨x, ?_⟩
  rw [absToSub_eq_cohPullback, cohPullback_apply_eq]
  exact hx

end LHCast

end

end GroupApproximation.CharClass
