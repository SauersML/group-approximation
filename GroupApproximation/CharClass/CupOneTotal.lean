import GroupApproximation.CharClass.ChernTotalRingOf
import GroupApproximation.CharClass.CupOneComm
import GroupApproximation.Meta.AxiomGuard

/-!
# Even classes of the cohomology ring over `K` commute with everything

Over a commutative ring `K` in which `1 ≠ -1` the cup product is graded commutative only up
to the Koszul sign, so `ChernTotalRingOf` gives `TotalHOf K X = ⨁ₙ Hⁿ(X; K)` a
`DirectSum.GRing` and deliberately no `mul_comm`.  What survives is the element-level form
of `cup_comm_of_even_left` (`CupOneComm`): a class vanishing in every odd degree commutes
with **every** element of the ring.  Chern classes, their products and their pullbacks have
this form, so every commutation the even side of the LIX program performs is an instance.

## Main declarations

* `TotalHOf.IsEven x` — every odd-degree component of `x` vanishes.
* `TotalHOf.isEven_zero`, `isEven_one`, `isEven_of`, `IsEven.add`, `IsEven.mul`,
  `IsEven.map` — the predicate is closed under the ring operations and pullback.
* `TotalHOf.commute_of_even_left` — a homogeneous class of even degree commutes with every
  element.
* `TotalHOf.mul_comm_of_isEven_left`, `mul_comm_of_isEven_right` — the corollary consumers use.
* `evenClassesCommute` — the closed endpoint.

Only the even-degree hypothesis is needed on one side: `a ⌣ b = (-1)^{pq} b ⌣ a`, and
`(-1)^{pq} = 1` as soon as `p` is even, whatever `q` is.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

noncomputable section

namespace TotalHOf

/-! ## 1. Components and the decomposition into homogeneous pieces -/

theorem component_apply (K : Type) [CommRing K] (X : TopCat.{0}) (n : ℕ) (x : TotalHOf K X) :
    component K X n x = x n := rfl

/-- A homogeneous class has no component in any other degree. -/
theorem component_of_ne (K : Type) [CommRing K] (X : TopCat.{0}) {i n : ℕ} (h : n ≠ i)
    (a : TotalPieceOf K X i) : component K X n (of K X i a) = 0 := by
  show (DirectSum.of (fun n : ℕ => TotalPieceOf K X n) i a) n = 0
  exact DirectSum.of_eq_of_ne i n a h

/-- Every element is the sum of its homogeneous pieces. -/
theorem sum_support_of' (K : Type) [CommRing K] (X : TopCat.{0})
    [∀ (i : ℕ) (a : TotalPieceOf K X i), Decidable (a ≠ 0)] (x : TotalHOf K X) :
    ∑ i ∈ DFinsupp.support x, of K X i (x i) = x :=
  DirectSum.sum_support_of x

/-- Transporting a class along an equality of degrees does not move it in the ring. -/
theorem of_cohCast (K : Type) [CommRing K] (X : TopCat.{0}) {m m' : ℕ} (h : m = m')
    (c : TotalPieceOf K X m) : of K X m' (cohCast h c) = of K X m c := by
  subst h
  rw [cohCast_rfl]

/-! ## 2. The predicate and its closure properties -/

/-- **An even class**: every odd-degree component vanishes. -/
def IsEven {K : Type} [CommRing K] {X : TopCat.{0}} (x : TotalHOf K X) : Prop :=
  ∀ n : ℕ, Odd n → component K X n x = 0

theorem isEven_zero (K : Type) [CommRing K] (X : TopCat.{0}) : IsEven (0 : TotalHOf K X) :=
  fun n _ => map_zero (component K X n)

theorem IsEven.add {K : Type} [CommRing K] {X : TopCat.{0}} {x y : TotalHOf K X}
    (hx : IsEven x) (hy : IsEven y) : IsEven (x + y) := by
  intro n hn
  rw [map_add, hx n hn, hy n hn, add_zero]

/-- A homogeneous class of even degree is even. -/
theorem isEven_of (K : Type) [CommRing K] (X : TopCat.{0}) {i : ℕ} (hi : Even i)
    (a : TotalPieceOf K X i) : IsEven (of K X i a) := by
  intro n hn
  refine component_of_ne K X (fun h => ?_) a
  subst h
  exact (Nat.not_odd_iff_even.mpr hi) hn

theorem isEven_one (K : Type) [CommRing K] (X : TopCat.{0}) : IsEven (1 : TotalHOf K X) := by
  rw [← of_one K X]
  exact isEven_of K X even_zero _

/-- **Products of even classes are even.** -/
theorem IsEven.mul {K : Type} [CommRing K] {X : TopCat.{0}} {x y : TotalHOf K X}
    (hx : IsEven x) (hy : IsEven y) : IsEven (x * y) := by
  classical
  intro n hn
  rw [← sum_support_of' K X x, ← sum_support_of' K X y, Finset.sum_mul, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Finset.mul_sum, map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rcases Nat.even_or_odd i with hi | hi
  · rcases Nat.even_or_odd j with hj | hj
    · rw [← of_mul]
      refine component_of_ne K X (fun h => ?_) _
      subst h
      exact (Nat.not_odd_iff_even.mpr (hi.add hj)) hn
    · have hyj : y j = 0 := hy j hj
      rw [hyj, map_zero, mul_zero, map_zero]
  · have hxi : x i = 0 := hx i hi
    rw [hxi, map_zero, zero_mul, map_zero]

/-- **Pullbacks of even classes are even.** -/
theorem IsEven.map {K : Type} [CommRing K] {X Y : TopCat.{0}} (f : X ⟶ Y) {x : TotalHOf K Y}
    (hx : IsEven x) : IsEven (map K f x) := by
  classical
  intro n hn
  rw [← sum_support_of' K Y x, map_sum, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [map_of]
  rcases Nat.even_or_odd i with hi | hi
  · refine component_of_ne K X (fun h => ?_) _
    subst h
    exact (Nat.not_odd_iff_even.mpr hi) hn
  · have hxi : x i = 0 := hx i hi
    rw [hxi, pull_zero, map_zero, map_zero]

/-! ## 3. Even classes commute with everything -/

/-- Two homogeneous classes commute when the first has even degree. -/
theorem commute_of_of_even_left (K : Type) [CommRing K] (X : TopCat.{0}) {m : ℕ} (hm : Even m)
    (a : TotalPieceOf K X m) (n : ℕ) (b : TotalPieceOf K X n) :
    Commute (of K X m a) (of K X n b) := by
  show of K X m a * of K X n b = of K X n b * of K X m a
  rw [← of_mul, ← of_mul, cup_comm_of_even_left hm a b, of_cohCast]

/-- **A homogeneous class of even degree commutes with every element.** -/
theorem commute_of_even_left (K : Type) [CommRing K] (X : TopCat.{0}) {m : ℕ} (hm : Even m)
    (a : TotalPieceOf K X m) (y : TotalHOf K X) : Commute (of K X m a) y := by
  induction y using DirectSum.induction_on with
  | zero => exact Commute.zero_right _
  | of n b => exact commute_of_of_even_left K X hm a n b
  | add y z hy hz => exact hy.add_right hz

/-- **An even class commutes with every element.** -/
theorem mul_comm_of_isEven_left {K : Type} [CommRing K] {X : TopCat.{0}} {x : TotalHOf K X}
    (hx : IsEven x) (y : TotalHOf K X) : x * y = y * x := by
  classical
  have hc : Commute (∑ i ∈ DFinsupp.support x, of K X i (x i)) y := by
    refine Commute.sum_left _ _ _ fun i _ => ?_
    show Commute (of K X i (x i)) y
    rcases Nat.even_or_odd i with hi | hi
    · exact commute_of_even_left K X hi (x i) y
    · have hxi : x i = 0 := hx i hi
      rw [hxi, map_zero]
      exact Commute.zero_left y
  rw [sum_support_of' K X x] at hc
  exact hc

/-- The same with the even class on the right. -/
theorem mul_comm_of_isEven_right {K : Type} [CommRing K] {X : TopCat.{0}} (x : TotalHOf K X)
    {y : TotalHOf K X} (hy : IsEven y) : x * y = y * x :=
  (mul_comm_of_isEven_left hy x).symm

end TotalHOf

/-! ## 4. Closed endpoint -/

/-- Over every commutative ring, an element of the cohomology ring vanishing in odd degrees
commutes with every element. -/
def EvenClassesCommute : Prop :=
  ∀ (K : Type) [CommRing K] (X : TopCat.{0}) (x y : TotalHOf K X),
    TotalHOf.IsEven x → x * y = y * x

theorem evenClassesCommute : EvenClassesCommute := by
  intro K _ X x y hx
  exact TotalHOf.mul_comm_of_isEven_left hx y

#audit_closed_axioms evenClassesCommute

end

end CharClass
end GroupApproximation
