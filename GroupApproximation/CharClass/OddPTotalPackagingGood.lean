import GroupApproximation.CharClass.OddPTotalPackagingDefs

/-!
# Packaging the reduced powers, part 2: junk-free classes and the total power as a ring map

A homogeneous class `c` of even degree `d` is *junk-free* (`IsGoodPiece`) when its total power
vanishes in every even degree that is not of the form `d + 2s(p − 1)`.  An element of the ring is
junk-free (`IsGood`) when each of its even pieces is.

* `IsGood` is closed under the ring operations.  For products, the total power is multiplicative
  on even classes, and the degrees `d + 2s(p − 1)` add.  So `good X` is a subring of the even part.
* It is natural along pullback and contains every class of degree two (`bad_two`).
* The total power on the whole ring is multiplicative on even classes, which makes `Ptot X` a ring
  endomorphism of the even part.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace OddPTotal

open CategoryTheory

noncomputable section

namespace TotalReducedPowers

variable {p : ℕ} (R : TotalReducedPowers p)

/-- A homogeneous class of degree `d` whose total power vanishes in the even degrees outside
`d + 2s(p − 1)`. -/
def IsGoodPiece (X : TopCat.{0}) (d : ℕ) (c : TotalPieceOf (ZMod p) X d) : Prop :=
  ∀ e : ℕ, e % 2 = 0 → ¬ GoodDeg p d e →
    TotalHOf.component (ZMod p) X e (ptotOf R.D X d c) = 0

/-- An element of the ring all of whose even pieces are junk-free. -/
def IsGood (X : TopCat.{0}) (x : TotalHOf (ZMod p) X) : Prop :=
  ∀ d : ℕ, d % 2 = 0 → R.IsGoodPiece X d (TotalHOf.component (ZMod p) X d x)

theorem isGoodPiece_zero (X : TopCat.{0}) (d : ℕ) : R.IsGoodPiece X d 0 := by
  intro e _ _
  rw [map_zero, map_zero]

theorem isGood_zero (X : TopCat.{0}) : R.IsGood X 0 := by
  intro d _
  rw [map_zero]
  exact R.isGoodPiece_zero X d

theorem isGood_add (X : TopCat.{0}) {x y : TotalHOf (ZMod p) X} (hx : R.IsGood X x)
    (hy : R.IsGood X y) : R.IsGood X (x + y) := by
  intro d hd e he hg
  rw [map_add, map_add, map_add, hx d hd e he hg, hy d hd e he hg, add_zero]

theorem isGood_neg (X : TopCat.{0}) {x : TotalHOf (ZMod p) X} (hx : R.IsGood X x) :
    R.IsGood X (-x) := by
  intro d hd e he hg
  rw [map_neg, map_neg, map_neg, hx d hd e he hg, neg_zero]

theorem isGood_sum (X : TopCat.{0}) {ι : Type*} (s : Finset ι) (f : ι → TotalHOf (ZMod p) X)
    (hf : ∀ i ∈ s, R.IsGood X (f i)) : R.IsGood X (∑ i ∈ s, f i) :=
  Finset.sum_induction f (R.IsGood X) (fun _ _ => R.isGood_add X) (R.isGood_zero X) hf

/-- A junk-free homogeneous class of even degree is junk-free in the ring. -/
theorem isGood_of (X : TopCat.{0}) {a : ℕ} (c : TotalPieceOf (ZMod p) X a)
    (hc : R.IsGoodPiece X a c) : R.IsGood X (TotalHOf.of (ZMod p) X a c) := by
  intro d _
  rw [component_of_eq_dite]
  by_cases h : a = d
  · subst h
    rw [dif_pos rfl]
    exact hc
  · rw [dif_neg h]
    exact R.isGoodPiece_zero X d

/-- **Products of junk-free classes of even degree are junk-free.** -/
theorem isGoodPiece_cup (X : TopCat.{0}) {a b : ℕ} (ha : a % 2 = 0) (hb : b % 2 = 0)
    {c : TotalPieceOf (ZMod p) X a} {c' : TotalPieceOf (ZMod p) X b}
    (hc : R.IsGoodPiece X a c) (hc' : R.IsGoodPiece X b c') :
    R.IsGoodPiece X (a + b) (cup c c') := by
  intro e _ hg
  rw [R.ptot_mul X (Nat.even_iff.mpr ha) (Nat.even_iff.mpr hb) c c']
  have hA := eq_sum_components (ZMod p) X (ptotOf R.D X a c) (Finset.range (p * a + 1))
    fun e₁ he₁ => R.component_ptotOf_of_lt X a e₁ c (by rw [Finset.mem_range] at he₁; omega)
  have hB := eq_sum_components (ZMod p) X (ptotOf R.D X b c') (Finset.range (p * b + 1))
    fun e₂ he₂ => R.component_ptotOf_of_lt X b e₂ c' (by rw [Finset.mem_range] at he₂; omega)
  rw [hA, hB, Finset.sum_mul_sum, map_sum]
  refine Finset.sum_eq_zero fun e₁ _ => ?_
  rw [map_sum]
  refine Finset.sum_eq_zero fun e₂ _ => ?_
  by_cases h₁ : e₁ % 2 = 0 ∧ GoodDeg p a e₁
  · by_cases h₂ : e₂ % 2 = 0 ∧ GoodDeg p b e₂
    · rw [← TotalHOf.of_mul, component_of_eq_dite, dif_neg]
      intro heq
      subst heq
      exact hg (goodDeg_add h₁.2 h₂.2)
    · have hz : TotalHOf.component (ZMod p) X e₂ (ptotOf R.D X b c') = 0 := by
        by_cases hodd : e₂ % 2 = 0
        · exact hc' e₂ hodd fun hgd => h₂ ⟨hodd, hgd⟩
        · exact R.component_ptotOf_of_odd X hb e₂ c' (by omega)
      rw [hz, map_zero, mul_zero, map_zero]
  · have hz : TotalHOf.component (ZMod p) X e₁ (ptotOf R.D X a c) = 0 := by
      by_cases hodd : e₁ % 2 = 0
      · exact hc e₁ hodd fun hgd => h₁ ⟨hodd, hgd⟩
      · exact R.component_ptotOf_of_odd X ha e₁ c (by omega)
    rw [hz, map_zero, zero_mul, map_zero]

theorem isGood_mul (X : TopCat.{0}) {x y : TotalHOf (ZMod p) X} (hxe : TotalHOf.IsEven x)
    (hye : TotalHOf.IsEven y) (hx : R.IsGood X x) (hy : R.IsGood X y) : R.IsGood X (x * y) := by
  classical
  rw [← TotalHOf.sum_support_of' (ZMod p) X x, ← TotalHOf.sum_support_of' (ZMod p) X y,
    Finset.sum_mul_sum]
  refine R.isGood_sum X _ _ fun a _ => R.isGood_sum X _ _ fun b _ => ?_
  rw [← TotalHOf.of_mul]
  by_cases ha : a % 2 = 0
  · by_cases hb : b % 2 = 0
    · exact R.isGood_of X _ (R.isGoodPiece_cup X ha hb (hx a ha) (hy b hb))
    · have hyb : y b = 0 := hye b (Nat.odd_iff.mpr (by omega))
      rw [hyb, cup_zero, map_zero]
      exact R.isGood_zero X
  · have hxa : x a = 0 := hxe a (Nat.odd_iff.mpr (by omega))
    rw [hxa, zero_cup, map_zero]
    exact R.isGood_zero X

theorem isGood_one (X : TopCat.{0}) : R.IsGood X 1 := by
  rw [← TotalHOf.of_one (ZMod p) X]
  refine R.isGood_of X _ fun e _ hg => ?_
  rw [R.component_ptotOf, dif_neg]
  rintro ⟨hle, _⟩
  apply hg
  have he : e = 0 := by omega
  subst he
  exact ⟨le_refl 0, by simp⟩

/-- **The junk-free even classes form a subring.** -/
def good (X : TopCat.{0}) : Subring (Gen.evenPart (ZMod p) X) where
  carrier := {x | R.IsGood X (x : TotalHOf (ZMod p) X)}
  mul_mem' {a b} ha hb := R.isGood_mul X a.2 b.2 ha hb
  one_mem' := R.isGood_one X
  add_mem' ha hb := R.isGood_add X ha hb
  zero_mem' := R.isGood_zero X
  neg_mem' hx := R.isGood_neg X hx

theorem mem_good {X : TopCat.{0}} {x : Gen.evenPart (ZMod p) X} :
    x ∈ R.good X ↔ R.IsGood X (x : TotalHOf (ZMod p) X) :=
  Iff.rfl

/-- Pullbacks of junk-free classes are junk-free. -/
theorem isGood_map {X Y : TopCat.{0}} (f : X ⟶ Y) {x : TotalHOf (ZMod p) Y}
    (hx : R.IsGood Y x) : R.IsGood X (TotalHOf.map (ZMod p) f x) := by
  intro d hd e he hg
  rw [component_map, R.ptotOf_natural, component_map, hx d hd e he hg, pull_zero]

/-- **Every class of degree two is junk-free**, from `bad_two`. -/
theorem isGoodPiece_two (X : TopCat.{0}) (c : TotalPieceOf (ZMod p) X 2) (hp : 2 ≤ p) :
    R.IsGoodPiece X 2 c := by
  intro e _ hg
  rw [R.component_ptotOf]
  by_cases h : e ≤ p * 2 ∧ (p * 2 - e) % 2 = 0
  · rw [dif_pos h, R.bad_two X c (p * 2 - e) h.2 ?_ ?_, cohCast_zero]
    · intro h0
      apply hg
      have he : e = p * 2 := by omega
      subst he
      refine ⟨by omega, ?_⟩
      rw [show p * 2 - 2 = 2 * (p - 1) by omega, Nat.mod_self]
    · intro h1
      apply hg
      have he : e = 2 := by omega
      subst he
      exact ⟨le_refl 2, by simp⟩
  · rw [dif_neg h]

/-! ## The total power as a ring map -/

theorem totalPtot_one (X : TopCat.{0}) : R.totalPtot X 1 = 1 := by
  rw [← TotalHOf.of_one (ZMod p) X, R.totalPtot_of, R.piecePtot_apply, if_pos rfl,
    R.ptotOf_apply, show p * 0 + 1 = 1 by simp, Finset.sum_range_one, if_pos rfl]
  exact (R.unit_zero X).trans (TotalHOf.of_one (ZMod p) X).symm

theorem totalPtot_mul (X : TopCat.{0}) {x y : TotalHOf (ZMod p) X} (hx : TotalHOf.IsEven x)
    (hy : TotalHOf.IsEven y) :
    R.totalPtot X (x * y) = R.totalPtot X x * R.totalPtot X y := by
  classical
  rw [← TotalHOf.sum_support_of' (ZMod p) X x, ← TotalHOf.sum_support_of' (ZMod p) X y,
    Finset.sum_mul_sum]
  simp only [map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← TotalHOf.of_mul, R.totalPtot_of, R.totalPtot_of, R.totalPtot_of,
    R.piecePtot_apply, R.piecePtot_apply, R.piecePtot_apply]
  by_cases ha : a % 2 = 0
  · by_cases hb : b % 2 = 0
    · rw [if_pos (by omega : (a + b) % 2 = 0), if_pos ha, if_pos hb]
      exact R.ptot_mul X (Nat.even_iff.mpr ha) (Nat.even_iff.mpr hb) _ _
    · have hyb : y b = 0 := hy b (Nat.odd_iff.mpr (by omega))
      simp only [hyb, cup_zero, map_zero, ite_self, mul_zero]
  · have hxa : x a = 0 := hx a (Nat.odd_iff.mpr (by omega))
    simp only [hxa, zero_cup, map_zero, ite_self, zero_mul]

/-- **The total power, as a ring endomorphism of the even part.** -/
def Ptot (X : TopCat.{0}) : Gen.evenPart (ZMod p) X →+* Gen.evenPart (ZMod p) X where
  toFun := Gen.evenRestrictAdd (R.totalPtot X) (fun x _ => R.totalPtot_isEven X x)
  map_one' := Subtype.ext (R.totalPtot_one X)
  map_mul' u v := Subtype.ext (R.totalPtot_mul X u.2 v.2)
  map_zero' := map_zero (Gen.evenRestrictAdd (R.totalPtot X) (fun x _ => R.totalPtot_isEven X x))
  map_add' := map_add (Gen.evenRestrictAdd (R.totalPtot X) (fun x _ => R.totalPtot_isEven X x))

theorem coe_Ptot (X : TopCat.{0}) (x : Gen.evenPart (ZMod p) X) :
    (R.Ptot X x : TotalHOf (ZMod p) X) = R.totalPtot X x :=
  rfl

/-- Naturality of the total power on the whole ring. -/
theorem totalPtot_map {X Y : TopCat.{0}} (f : X ⟶ Y) (x : TotalHOf (ZMod p) Y) :
    R.totalPtot X (TotalHOf.map (ZMod p) f x) = TotalHOf.map (ZMod p) f (R.totalPtot Y x) := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of d c =>
    show R.totalPtot X (TotalHOf.map (ZMod p) f (TotalHOf.of (ZMod p) Y d c))
      = TotalHOf.map (ZMod p) f (R.totalPtot Y (TotalHOf.of (ZMod p) Y d c))
    rw [TotalHOf.map_of, R.totalPtot_of, R.totalPtot_of, R.piecePtot_apply, R.piecePtot_apply]
    by_cases hd : d % 2 = 0
    · rw [if_pos hd, if_pos hd, R.ptotOf_natural]
    · rw [if_neg hd, if_neg hd, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, ← map_add]

end TotalReducedPowers

end

end OddPTotal

#audit_axioms OddPTotal.TotalReducedPowers.isGoodPiece_cup
#audit_axioms OddPTotal.TotalReducedPowers.good
#audit_axioms OddPTotal.TotalReducedPowers.isGood_map
#audit_axioms OddPTotal.TotalReducedPowers.isGoodPiece_two
#audit_axioms OddPTotal.TotalReducedPowers.Ptot
#audit_axioms OddPTotal.TotalReducedPowers.totalPtot_map

end CharClass
end GroupApproximation
