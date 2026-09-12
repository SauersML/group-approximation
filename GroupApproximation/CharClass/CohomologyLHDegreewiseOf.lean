import GroupApproximation.CharClass.CohomologyLHRestrict
import GroupApproximation.Meta.AxiomGuard

/-!
# Reading a Leray–Hirsch instance degreewise, and restriction below the top, over any ring

Lane `lix-coeff` of the STW Problem LIX strengthening
(`notes/LIX_STRONGER_PROGRAM_2026-09-10.md` §1.5).

Additive twin of `CohomologyLHDegreewise` and `CohomologyLHRestrict` with coefficients in a
commutative ring `K`.  The Leray–Hirsch layer underneath (`lhDomainCard`, `lhMap`, `lhTerm`,
`LerayHirschGraded`, `lhTerm_of_le`, `pull_cupPowE`) is already generic in `K`; the two `F₂` files
fixed `K = ZMod 2` only in their statements.  Every proof is the `F₂` proof: the transports are
`rfl` on underlying naturals, and restriction carries a column term to a column term by `pull_cup`
and `pull_cupPowE`.  No field is needed anywhere.

The index equivalences `lhIndexEquiv`, `lhIndexEquiv2` and the cardinal computations
`lhDomainCard_succ_two_mul`, `lhDomainCard_succ_two_mul_sub_one`, `lhDomainCard_two_mul_sub_one`
carry no coefficients and are the `F₂` files' own.

The coefficient ring is explicit in the two transports, whose arguments do not determine it, and
implicit elsewhere, where the class `ξ` does.

## Main declarations

* `LHCast.lhDomainEquivOf`, `LHCast.lhMap_eq_sum_lhTermOf`, `LHCast.bijective_sum_lhTerm_of_gradedOf`,
  `LHCast.bijective_sum_lhTerm_topOf` — the degreewise reading.
* `LHCast.lhDomainEquiv2Of`, `LHCast.bijective_sum_lhTerm_of_cardOf`, `LHCast.pull_lhTermOf`,
  `LHCast.bijective_pull_of_gradedOf`, `LHCast.absToSub_surjective_of_gradedOf` — restriction one
  degree below the top.
* `KnHemi.pull_cohCastOf` — pullback commutes with the degree cast.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

namespace KnHemi

/-- Pullback commutes with the degree cast, over any ring. -/
theorem pull_cohCastOf {K : Type} [CommRing K] {X Z : TopCat.{0}} (f : X ⟶ Z) {m m' : ℕ}
    (h : m = m') (a : Hmod K Z m) : pull f m' (cohCast h a) = cohCast h (pull f m a) := by
  subst h
  rfl

end KnHemi

namespace LHCast

open LH

/-! ## 1. The coefficient transport at the rank -/

/-- **The dependent transport over `K`**, as a linear equivalence. -/
def lhDomainEquivOf (K : Type) [CommRing K] (X : TopCat.{0}) (r n : ℕ)
    (h : lhDomainCard r n = r) :
    ((i : Fin (lhDomainCard r n)) → Hmod K X (n - 2 * (i : ℕ)))
      ≃ₗ[K] ((i : Fin r) → Hmod K X (n - 2 * (i : ℕ))) where
  toFun a i := a ((lhIndexEquiv r n h).symm i)
  invFun b i := b (lhIndexEquiv r n h i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv a := by funext i; rfl
  right_inv b := by funext i; rfl

set_option maxHeartbeats 1000000 in
/-- **The combination is the same after reindexing**, over `K`. -/
theorem lhMap_eq_sum_lhTermOf {K : Type} [CommRing K] {X P : TopCat.{0}} (π : P ⟶ X)
    (ξ : Hmod K P 2) (r n : ℕ) (h : lhDomainCard r n = r)
    (a : (i : Fin (lhDomainCard r n)) → Hmod K X (n - 2 * (i : ℕ))) :
    lhMap π ξ r n a
      = ∑ i : Fin r, lhTerm π ξ n (i : ℕ) (lhDomainEquivOf K X r n h a i) := by
  simp only [lhMap]
  refine Fintype.sum_equiv (lhIndexEquiv r n h) _ _ (fun i => ?_)
  exact (lhTerm_of_le π ξ (two_mul_le_of_lhDomain i) (a i)).symm

set_option maxHeartbeats 1000000 in
/-- **A Leray–Hirsch instance over `K`, read at the rank instead of at the cardinal.** -/
theorem bijective_sum_lhTerm_of_gradedOf {K : Type} [CommRing K] {X P : TopCat.{0}}
    {π : P ⟶ X} {ξ : Hmod K P 2} {r : ℕ} (L : LerayHirschGraded π ξ r) (n : ℕ)
    (h : lhDomainCard r n = r) :
    Function.Bijective (fun a : (i : Fin r) → Hmod K X (n - 2 * (i : ℕ)) =>
      ∑ i : Fin r, lhTerm π ξ n (i : ℕ) (a i)) := by
  have hfun : (fun a : (i : Fin r) → Hmod K X (n - 2 * (i : ℕ)) =>
      ∑ i : Fin r, lhTerm π ξ n (i : ℕ) (a i))
      = (lhMap π ξ r n) ∘ (lhDomainEquivOf K X r n h).symm := by
    funext a
    have hb := lhMap_eq_sum_lhTermOf π ξ r n h ((lhDomainEquivOf K X r n h).symm a)
    rw [(lhDomainEquivOf K X r n h).apply_symm_apply] at hb
    exact hb.symm
  rw [hfun]
  exact (L.bij n).comp (lhDomainEquivOf K X r n h).symm.bijective

/-- **The shape the Thom datum consumes, over `K`**: the coefficients of a rank-`(r+1)` instance
in degree `2 * r`, indexed by `Fin (r + 1)`. -/
theorem bijective_sum_lhTerm_topOf {K : Type} [CommRing K] {X P : TopCat.{0}} {π : P ⟶ X}
    {ξ : Hmod K P 2} {r : ℕ} (L : LerayHirschGraded π ξ (r + 1)) :
    Function.Bijective (fun a : (i : Fin (r + 1)) → Hmod K X (2 * r - 2 * (i : ℕ)) =>
      ∑ i : Fin (r + 1), lhTerm π ξ (2 * r) (i : ℕ) (a i)) :=
  bijective_sum_lhTerm_of_gradedOf L (2 * r) (lhDomainCard_succ_two_mul r)

/-! ## 2. The transport at an arbitrary target cardinal -/

/-- The coefficient transport at an arbitrary target cardinal, over `K`. -/
def lhDomainEquiv2Of (K : Type) [CommRing K] (X : TopCat.{0}) (R n s : ℕ)
    (h : lhDomainCard R n = s) :
    ((i : Fin (lhDomainCard R n)) → Hmod K X (n - 2 * (i : ℕ)))
      ≃ₗ[K] ((i : Fin s) → Hmod K X (n - 2 * (i : ℕ))) where
  toFun a i := a ((lhIndexEquiv2 R n s h).symm i)
  invFun b i := b (lhIndexEquiv2 R n s h i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv a := by funext i; rfl
  right_inv b := by funext i; rfl

set_option maxHeartbeats 1000000 in
theorem lhMap_eq_sum_lhTerm2Of {K : Type} [CommRing K] {X P : TopCat.{0}} (π : P ⟶ X)
    (ξ : Hmod K P 2) (R n s : ℕ) (h : lhDomainCard R n = s)
    (a : (i : Fin (lhDomainCard R n)) → Hmod K X (n - 2 * (i : ℕ))) :
    lhMap π ξ R n a
      = ∑ i : Fin s, lhTerm π ξ n (i : ℕ) (lhDomainEquiv2Of K X R n s h a i) := by
  simp only [lhMap]
  refine Fintype.sum_equiv (lhIndexEquiv2 R n s h) _ _ (fun i => ?_)
  exact (lhTerm_of_le π ξ (two_mul_le_of_lhDomain i) (a i)).symm

set_option maxHeartbeats 1000000 in
/-- The coefficient description at a degree whose cardinal is `s`, over `K`. -/
theorem bijective_sum_lhTerm_of_cardOf {K : Type} [CommRing K] {X P : TopCat.{0}} {π : P ⟶ X}
    {ξ : Hmod K P 2} {R : ℕ} (L : LerayHirschGraded π ξ R) (n s : ℕ)
    (h : lhDomainCard R n = s) :
    Function.Bijective (fun a : (i : Fin s) → Hmod K X (n - 2 * (i : ℕ)) =>
      ∑ i : Fin s, lhTerm π ξ n (i : ℕ) (a i)) := by
  have hfun : (fun a : (i : Fin s) → Hmod K X (n - 2 * (i : ℕ)) =>
      ∑ i : Fin s, lhTerm π ξ n (i : ℕ) (a i))
      = (lhMap π ξ R n) ∘ (lhDomainEquiv2Of K X R n s h).symm := by
    funext a
    have hb := lhMap_eq_sum_lhTerm2Of π ξ R n s h ((lhDomainEquiv2Of K X R n s h).symm a)
    rw [(lhDomainEquiv2Of K X R n s h).apply_symm_apply] at hb
    exact hb.symm
  rw [hfun]
  exact (L.bij n).comp (lhDomainEquiv2Of K X R n s h).symm.bijective

/-! ## 3. Restriction carries a column term to a column term -/

set_option maxHeartbeats 1000000 in
/-- **A column term restricts to the column term at the same index**, over `K`. -/
theorem pull_lhTermOf {K : Type} [CommRing K] {X P Q : TopCat.{0}} (f : Q ⟶ P) (π : P ⟶ X)
    (π' : Q ⟶ X) (hπ : f ≫ π = π') (ξ : Hmod K P 2) (ξ' : Hmod K Q 2)
    (hξ : pull f 2 ξ = ξ') (n i : ℕ) (a : Hmod K X (n - 2 * i)) :
    pull f n (lhTerm π ξ n i a) = lhTerm π' ξ' n i a := by
  by_cases hi : 2 * i ≤ n
  · rw [lhTerm_of_le π ξ hi, lhTerm_of_le π' ξ' hi, KnHemi.pull_cohCastOf, pull_cup,
      ← pull_comp, hπ, pull_cupPowE, hξ]
  · rw [lhTerm_of_gt π ξ hi, lhTerm_of_gt π' ξ' hi, pull_zero]

/-! ## 4. The restriction one degree below the top is bijective -/

set_option maxHeartbeats 1000000 in
/-- **The restriction one degree below the top is bijective**, over `K`. -/
theorem bijective_pull_of_gradedOf {K : Type} [CommRing K] {X P Q : TopCat.{0}} (f : Q ⟶ P)
    (π : P ⟶ X) (π' : Q ⟶ X) (hπ : f ≫ π = π')
    (ξ : Hmod K P 2) (ξ' : Hmod K Q 2) (hξ : pull f 2 ξ = ξ')
    (r : ℕ) (hr : 1 ≤ r)
    (L : LerayHirschGraded π ξ (r + 1)) (L' : LerayHirschGraded π' ξ' r) :
    Function.Bijective (pull (K := K) f (2 * r - 1)) := by
  have hF : Function.Bijective
      (fun a : (i : Fin r) → Hmod K X (2 * r - 1 - 2 * (i : ℕ)) =>
        ∑ i : Fin r, lhTerm π ξ (2 * r - 1) (i : ℕ) (a i)) :=
    bijective_sum_lhTerm_of_cardOf L (2 * r - 1) r
      (lhDomainCard_succ_two_mul_sub_one r hr)
  have hG : Function.Bijective
      (fun a : (i : Fin r) → Hmod K X (2 * r - 1 - 2 * (i : ℕ)) =>
        ∑ i : Fin r, lhTerm π' ξ' (2 * r - 1) (i : ℕ) (a i)) :=
    bijective_sum_lhTerm_of_cardOf L' (2 * r - 1) r
      (lhDomainCard_two_mul_sub_one r hr)
  have hcomp : (pull (K := K) f (2 * r - 1)) ∘
      (fun a : (i : Fin r) → Hmod K X (2 * r - 1 - 2 * (i : ℕ)) =>
        ∑ i : Fin r, lhTerm π ξ (2 * r - 1) (i : ℕ) (a i))
      = fun a : (i : Fin r) → Hmod K X (2 * r - 1 - 2 * (i : ℕ)) =>
        ∑ i : Fin r, lhTerm π' ξ' (2 * r - 1) (i : ℕ) (a i) := by
    funext a
    show pull f (2 * r - 1) (∑ i : Fin r, lhTerm π ξ (2 * r - 1) (i : ℕ) (a i)) = _
    have hsum : pull f (2 * r - 1)
        (∑ i : Fin r, lhTerm π ξ (2 * r - 1) (i : ℕ) (a i))
        = ∑ i : Fin r, pull f (2 * r - 1) (lhTerm π ξ (2 * r - 1) (i : ℕ) (a i)) :=
      map_sum (pullLinear (K := K) f (2 * r - 1)) _ _
    rw [hsum]
    exact Finset.sum_congr rfl
      (fun i _ => pull_lhTermOf f π π' hπ ξ ξ' hξ (2 * r - 1) (i : ℕ) (a i))
  have hGF : Function.Bijective ((pull (K := K) f (2 * r - 1)) ∘
      (fun a : (i : Fin r) → Hmod K X (2 * r - 1 - 2 * (i : ℕ)) =>
        ∑ i : Fin r, lhTerm π ξ (2 * r - 1) (i : ℕ) (a i))) := by
    rw [hcomp]
    exact hG
  exact (Function.Bijective.of_comp_iff (pull (K := K) f (2 * r - 1)) hF).mp hGF

/-- **The Thom datum's input, over `K`.**  The restriction of the pair one degree below the top
is onto. -/
theorem absToSub_surjective_of_gradedOf {K : Type} [CommRing K] {X P : TopCat.{0}} (Z : Set P)
    (π : P ⟶ X) (π' : TopCat.of Z ⟶ X) (hπ : sInclusion Z ≫ π = π')
    (ξ : Hmod K P 2) (ξ' : Hmod K (TopCat.of Z) 2)
    (hξ : pull (sInclusion Z) 2 ξ = ξ')
    (r : ℕ) (hr : 1 ≤ r)
    (L : LerayHirschGraded π ξ (r + 1)) (L' : LerayHirschGraded π' ξ' r) :
    Function.Surjective (absToSub K Z (2 * r - 1)).hom := by
  intro y
  obtain ⟨x, hx⟩ :=
    (bijective_pull_of_gradedOf (sInclusion Z) π π' hπ ξ ξ' hξ r hr L L').2 y
  refine ⟨x, ?_⟩
  rw [absToSub_eq_cohPullbackOf]
  exact hx

end LHCast

end

/-! Audited on every build. -/

#audit_axioms LHCast.bijective_sum_lhTerm_of_gradedOf
#audit_axioms LHCast.bijective_pull_of_gradedOf
#audit_axioms LHCast.absToSub_surjective_of_gradedOf

end GroupApproximation.CharClass
