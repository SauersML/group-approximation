import GroupApproximation.CharClass.CohomologyLHDegreewiseOf
import GroupApproximation.CharClass.CohomologyLHRingTerm
import GroupApproximation.CharClass.ChernClassesOf
import GroupApproximation.CharClass.CupOneTotal
import GroupApproximation.Meta.AxiomGuard

/-!
# `lhFunOf` in a degree is `lhMap`, over any coefficient ring

Lane `lix-coeff` of the STW Problem LIX strengthening
(`notes/LIX_STRONGER_PROGRAM_2026-09-10.md` §1.5).

Additive twin of `CohomologyLHRingPieces`, `CohomologyLHRingTerm` and `CohomologyLHRingComponent`
with coefficients in a commutative ring `K`: the degree-`n` component of the ring-level Leray–Hirsch
combination `lhFunOf K π r ξ c = ∑ π^*(c i) · ξ^i` (lane `lix-lh`'s `ChernClassesOf`) is the
degreewise combination `lhMap` applied to the componentwise coefficients.

**The sign-free route.**  The `F₂` file moves `ξ^i` to the left with `mul_comm`, reads the
component of a left-concentrated product, and moves it back with the unsigned `cup_comm`.  Over `K`
`TotalHOf K P` is only graded commutative, so this file reads the component of a
**right**-concentrated product instead,

```text
component (m + i) (z · of i w) = component m z ⌣ w,
```

and the ring term `π^*(c i) · ξ^i` lands directly on the degreewise term `π^*(a) ⌣ ξ^i` of `lhTerm`,
in the same order.  No Koszul sign enters anywhere in the bridge.

The index bookkeeping (`lhDomainCard`, `mem_lhDomain_iff`, `lhDomainCard_le`) is coefficient-free
and is the `F₂` files' own.

## Main declarations

* `LHCast.totalHOf_of_pow` — the power of the degree-two generator is the cup power.
* `LHCast.sum_lhTerm_truncateOf` — the ring-level and degreewise ranges of summation agree.
* `LHCast.component_mapOf`, `LHCast.component_mul_ofOf`, `LHCast.component_mul_of_ltOf`.
* `LHCast.component_lhFunOf_term_gen` — one term of `lhFunOf` at any degree.
* `LHCast.degFunOf`, `LHCast.component_lhFunOf` — **the core lemma**.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

namespace LHCast

open LH

variable {X P : TopCat.{0}}

/-! ## 1. Powers of the generator -/

/-- **The `i`-th power of the degree-two generator is the cup power**, concentrated in degree
`2i`, over any ring. -/
theorem totalHOf_of_pow (K : Type) [CommRing K] (ξ : Hmod K P 2) :
    ∀ i : ℕ, TotalHOf.of K P 2 ξ ^ i = TotalHOf.of K P (2 * i) (cupPowE ξ i) := by
  intro i
  induction i with
  | zero => rw [pow_zero, cupPowE_zero, TotalHOf.of_one]
  | succ j ih =>
    show TotalHOf.of K P 2 ξ ^ (j + 1) = TotalHOf.of K P (2 * j + 2) (cupPowE ξ (j + 1))
    rw [pow_succ, ih, cupPowE_succ, TotalHOf.of_mul]

/-! ## 2. The two ranges of summation -/

/-- **The ring-level range and the degreewise range agree**, over any ring: the omitted terms have
`2i > n`, where `lhTerm` is zero by definition. -/
theorem sum_lhTerm_truncateOf {K : Type} [CommRing K] (π : P ⟶ X) (ξ : Hmod K P 2) (r n : ℕ)
    (f : (i : ℕ) → Hmod K X (n - 2 * i)) :
    ∑ i : Fin r, lhTerm π ξ n (i : ℕ) (f (i : ℕ))
      = ∑ i : Fin (lhDomainCard r n), lhTerm π ξ n (i : ℕ) (f (i : ℕ)) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => lhTerm π ξ n i (f i)) r,
    Fin.sum_univ_eq_sum_range (fun i => lhTerm π ξ n i (f i)) (lhDomainCard r n)]
  refine (Finset.sum_subset (fun x hx => ?_) ?_).symm
  · simp only [Finset.mem_range] at hx ⊢
    exact lt_of_lt_of_le hx (lhDomainCard_le r n)
  intro i hi hni
  simp only [Finset.mem_range] at hi hni
  refine lhTerm_of_gt π ξ ?_ (f i)
  unfold lhDomainCard at hni
  omega

/-! ## 3. Components of pullbacks and of right-concentrated products -/

/-- The component of a pullback is the pullback of the component, over any ring. -/
theorem component_mapOf (K : Type) [CommRing K] {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (c : TotalHOf K Y) :
    TotalHOf.component K X n (TotalHOf.map K f c) = pull f n (TotalHOf.component K Y n c) := by
  induction c using DirectSum.induction_on with
  | zero => simp only [map_zero, pull_zero]
  | of j a =>
    show TotalHOf.component K X n (TotalHOf.map K f (TotalHOf.of K Y j a))
      = pull f n (TotalHOf.component K Y n (TotalHOf.of K Y j a))
    rw [TotalHOf.map_of]
    rcases eq_or_ne n j with rfl | hne
    · rw [TotalHOf.component_of, TotalHOf.component_of]
    · rw [TotalHOf.component_of_ne K X hne, TotalHOf.component_of_ne K Y hne, pull_zero]
  | add u v hu hv => simp only [map_add, hu, hv, pull_add]

/-- **The component of a right-concentrated product**, over any ring:
`component (m + i) (z · of i w) = component m z ⌣ w`.  No commutation is performed. -/
theorem component_mul_ofOf (K : Type) [CommRing K] (X : TopCat.{0}) (m i : ℕ) (z : TotalHOf K X)
    (w : TotalPieceOf K X i) :
    TotalHOf.component K X (m + i) (z * TotalHOf.of K X i w)
      = cup (TotalHOf.component K X m z) w := by
  induction z using DirectSum.induction_on with
  | zero => simp only [zero_mul, map_zero, zero_cup]
  | of j c =>
    show TotalHOf.component K X (m + i) (TotalHOf.of K X j c * TotalHOf.of K X i w)
      = cup (TotalHOf.component K X m (TotalHOf.of K X j c)) w
    rw [← TotalHOf.of_mul]
    rcases eq_or_ne j m with rfl | hjm
    · rw [TotalHOf.component_of, TotalHOf.component_of]
    · rw [TotalHOf.component_of_ne K X (show m + i ≠ j + i by omega),
        TotalHOf.component_of_ne K X hjm.symm, zero_cup]
  | add z₁ z₂ h₁ h₂ => simp only [add_mul, map_add, h₁, h₂, cup_add_left]

/-- The same product in a degree it cannot reach: below `i` there is nothing. -/
theorem component_mul_of_ltOf (K : Type) [CommRing K] (X : TopCat.{0}) (n i : ℕ)
    (z : TotalHOf K X) (w : TotalPieceOf K X i) (hn : n < i) :
    TotalHOf.component K X n (z * TotalHOf.of K X i w) = 0 := by
  induction z using DirectSum.induction_on with
  | zero => rw [zero_mul, map_zero]
  | of j c =>
    show TotalHOf.component K X n (TotalHOf.of K X j c * TotalHOf.of K X i w) = 0
    rw [← TotalHOf.of_mul]
    exact TotalHOf.component_of_ne K X (by omega) _
  | add z₁ z₂ h₁ h₂ => rw [add_mul, map_add, h₁, h₂, add_zero]

/-! ## 4. One term of `lhFunOf` -/

/-- **One term of `lhFunOf`, in a degree**, over any ring: the coefficient is read `2i` degrees
below, and the order of the cup is the order of `lhTerm`. -/
theorem component_lhFunOf_term (K : Type) [CommRing K] (π : P ⟶ X) (ξ : Hmod K P 2) (i m : ℕ)
    (z : TotalHOf K X) :
    TotalHOf.component K P (m + 2 * i) (TotalHOf.map K π z * TotalHOf.of K P 2 ξ ^ i)
      = cup (pull π m (TotalHOf.component K X m z)) (cupPowE ξ i) := by
  rw [totalHOf_of_pow, component_mul_ofOf, component_mapOf]

/-- The same term in a degree it cannot reach. -/
theorem component_lhFunOf_term_lt (K : Type) [CommRing K] (π : P ⟶ X) (ξ : Hmod K P 2)
    (i n : ℕ) (hn : n < 2 * i) (z : TotalHOf K X) :
    TotalHOf.component K P n (TotalHOf.map K π z * TotalHOf.of K P 2 ξ ^ i) = 0 := by
  rw [totalHOf_of_pow]
  exact component_mul_of_ltOf K P n (2 * i) _ _ hn

/-- One term, with its degree carried as an equation so that it can be substituted. -/
theorem component_lhFunOf_term' (K : Type) [CommRing K] (π : P ⟶ X) (ξ : Hmod K P 2)
    (i m n : ℕ) (hn : m + 2 * i = n) (z : TotalHOf K X) :
    TotalHOf.component K P n (TotalHOf.map K π z * TotalHOf.of K P 2 ξ ^ i)
      = cohCast hn (cup (pull π m (TotalHOf.component K X m z)) (cupPowE ξ i)) := by
  subst hn
  rw [component_lhFunOf_term, CharClass.cohCast_self]

/-- **One term of `lhFunOf` at any degree**, over any ring. -/
theorem component_lhFunOf_term_gen (K : Type) [CommRing K] (π : P ⟶ X) (ξ : Hmod K P 2)
    (n i : ℕ) (z : TotalHOf K X) :
    TotalHOf.component K P n (TotalHOf.map K π z * TotalHOf.of K P 2 ξ ^ i)
      = lhTerm π ξ n i (TotalHOf.component K X (n - 2 * i) z) := by
  by_cases hi : 2 * i ≤ n
  · rw [component_lhFunOf_term' K π ξ i (n - 2 * i) n (Nat.sub_add_cancel hi) z,
      lhTerm_of_le π ξ hi]
  · rw [lhTerm_of_gt π ξ hi, component_lhFunOf_term_lt K π ξ i n (by omega) z]

/-! ## 5. The componentwise coefficients, and the core lemma -/

/-- The componentwise coefficients of a tuple of ring elements, as a **total** function of the
index, over any ring. -/
def degFunOf (K : Type) [CommRing K] (X : TopCat.{0}) (r n : ℕ) (c : Fin r → TotalHOf K X) :
    (i : ℕ) → Hmod K X (n - 2 * i) :=
  fun i => if h : i < r then TotalHOf.component K X (n - 2 * i) (c ⟨i, h⟩) else 0

set_option maxHeartbeats 1000000 in
/-- **The degree-`n` component of `lhFunOf` is `lhMap` on the componentwise coefficients**, over
any ring. -/
theorem component_lhFunOf (K : Type) [CommRing K] (π : P ⟶ X) (ξ : Hmod K P 2) (r n : ℕ)
    (c : Fin r → TotalHOf K X) :
    TotalHOf.component K P n (lhFunOf K π r ξ c)
      = lhMap π ξ r n (fun i => degFunOf K X r n c (i : ℕ)) := by
  have hR : lhMap π ξ r n (fun i => degFunOf K X r n c (i : ℕ))
      = ∑ i : Fin r, lhTerm π ξ n (i : ℕ) (degFunOf K X r n c (i : ℕ)) := by
    rw [lhMap_eq_sum_lhTerm2Of π ξ r n (lhDomainCard r n) rfl]
    exact (sum_lhTerm_truncateOf π ξ r n (degFunOf K X r n c)).symm
  rw [hR]
  show TotalHOf.component K P n
    (∑ i : Fin r, TotalHOf.map K π (c i) * TotalHOf.of K P 2 ξ ^ (i : ℕ)) = _
  rw [map_sum (TotalHOf.component K P n)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [component_lhFunOf_term_gen]
  congr 1
  rw [degFunOf, dif_pos i.isLt]

end LHCast

end

/-! Audited on every build. -/

#audit_axioms LHCast.component_mul_ofOf
#audit_axioms LHCast.component_lhFunOf

end GroupApproximation.CharClass
