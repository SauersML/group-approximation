import GroupApproximation.CharClass.LerayHirschInduction
import GroupApproximation.CharClass.LerayHirschDegree

/-!
# From the ladder's column to the published Leray–Hirsch interface

The ladder is run on `lhDomain X r n`, the subgroup of `Fin r`-indexed families
that vanish where the degree does not admit them, because that index type does
not change with `n` and so the connecting map keeps its shape.  The interface
every consumer sees, `LerayHirschGraded`, is stated on `Fin (lhDomainCard r n)`,
where the index set is cut down instead of the families.  This file is the
isomorphism between the two, and the transfer of bijectivity across it.

`lhExtend` extends a family indexed by the present summands by zero; it is a
bijection onto `lhDomain`, and `lhMap_eq_lhSum` says the two Leray–Hirsch
combinations agree along it.  Both sums are compared through a single
natural-number-indexed function, `lhTermCard`, so no reindexing of a dependent
family is ever needed.

## Main declarations

* `lhExtend`, `lhRestrictFun`, `bijective_lhExtend` — the isomorphism.
* `lhMap_eq_lhSum` — the two combinations agree.
* `bijective_lhMap_of_lhSum`, `bijective_lhSum_of_lhMap` — transfer, both ways.
* `lerayHirschGraded_of_bijective` — **the ladder's output in the published
  interface**.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory

noncomputable section

variable {X P : TopCat.{0}}

/-! ## 1. The index bijection -/

theorem lhDomainCard_le (r n : ℕ) : lhDomainCard r n ≤ r := min_le_left _ _

/-- A summand of the `Fin r`-indexed family is present exactly when its index is
below `lhDomainCard r n`. -/
theorem lt_card_iff (r n : ℕ) (j : Fin r) :
    (j : ℕ) < lhDomainCard r n ↔ 2 * (j : ℕ) ≤ n := by
  have hj : (j : ℕ) < r := j.2
  unfold lhDomainCard
  omega

/-- Extend a family indexed by the present summands by zero. -/
def lhExtend (X : TopCat.{0}) (r n : ℕ)
    (d : (i : Fin (lhDomainCard r n)) → Hmod2 X (n - 2 * (i : ℕ))) :
    lhDomain X r n :=
  ⟨fun j => if h : (j : ℕ) < lhDomainCard r n then d ⟨(j : ℕ), h⟩ else 0, by
    intro j hj
    have hnot : ¬ ((j : ℕ) < lhDomainCard r n) := by
      rw [lt_card_iff]
      omega
    exact dif_neg hnot⟩

theorem lhExtend_apply_of_lt (X : TopCat.{0}) (r n : ℕ)
    (d : (i : Fin (lhDomainCard r n)) → Hmod2 X (n - 2 * (i : ℕ))) {j : Fin r}
    (h : (j : ℕ) < lhDomainCard r n) :
    ((lhExtend X r n d : (i : Fin r) → Hmod2 X (n - 2 * (i : ℕ))) j)
      = d ⟨(j : ℕ), h⟩ :=
  dif_pos h

theorem lhExtend_apply_of_ge (X : TopCat.{0}) (r n : ℕ)
    (d : (i : Fin (lhDomainCard r n)) → Hmod2 X (n - 2 * (i : ℕ))) {j : Fin r}
    (h : ¬ ((j : ℕ) < lhDomainCard r n)) :
    ((lhExtend X r n d : (i : Fin r) → Hmod2 X (n - 2 * (i : ℕ))) j) = 0 :=
  dif_neg h

/-- Restrict a column element to the present summands. -/
def lhRestrictFun (X : TopCat.{0}) (r n : ℕ) (c : lhDomain X r n) :
    (i : Fin (lhDomainCard r n)) → Hmod2 X (n - 2 * (i : ℕ)) :=
  fun i => (c : (j : Fin r) → Hmod2 X (n - 2 * (j : ℕ)))
    (Fin.castLE (lhDomainCard_le r n) i)

theorem lhRestrictFun_lhExtend (X : TopCat.{0}) (r n : ℕ)
    (d : (i : Fin (lhDomainCard r n)) → Hmod2 X (n - 2 * (i : ℕ))) :
    lhRestrictFun X r n (lhExtend X r n d) = d := by
  funext i
  exact lhExtend_apply_of_lt X r n d (j := Fin.castLE (lhDomainCard_le r n) i) i.2

theorem lhExtend_lhRestrictFun (X : TopCat.{0}) (r n : ℕ) (c : lhDomain X r n) :
    lhExtend X r n (lhRestrictFun X r n c) = c := by
  refine lhDomain_ext fun j => ?_
  by_cases h : (j : ℕ) < lhDomainCard r n
  · exact lhExtend_apply_of_lt X r n _ h
  · rw [lhExtend_apply_of_ge X r n _ h]
    refine (lhDomain_vanish c j ?_).symm
    rw [lt_card_iff] at h
    omega

theorem bijective_lhExtend (X : TopCat.{0}) (r n : ℕ) :
    Function.Bijective (lhExtend X r n) := by
  constructor
  · intro d d' h
    have h' := congrArg (lhRestrictFun X r n) h
    rwa [lhRestrictFun_lhExtend, lhRestrictFun_lhExtend] at h'
  · exact fun c => ⟨lhRestrictFun X r n c, lhExtend_lhRestrictFun X r n c⟩

/-! ## 2. Both combinations, through one natural-number-indexed summand -/

/-- The Leray–Hirsch summand as a function of a natural-number index.  Comparing
the two sums through this avoids reindexing a dependent family. -/
def lhTermCard (π : P ⟶ X) (ξ : Hmod2 P 2) (r n : ℕ)
    (d : (i : Fin (lhDomainCard r n)) → Hmod2 X (n - 2 * (i : ℕ))) (k : ℕ) :
    Hmod2 P n :=
  if h : k < lhDomainCard r n then
    cohCast
      (Nat.sub_add_cancel
        (two_mul_le_of_lhDomain (⟨k, h⟩ : Fin (lhDomainCard r n))))
      (cup (pull π (n - 2 * k) (d ⟨k, h⟩)) (cupPowE ξ k))
  else 0

theorem lhTermCard_of_lt (π : P ⟶ X) (ξ : Hmod2 P 2) (r n : ℕ)
    (d : (i : Fin (lhDomainCard r n)) → Hmod2 X (n - 2 * (i : ℕ))) {k : ℕ}
    (h : k < lhDomainCard r n) :
    lhTermCard π ξ r n d k
      = cohCast
        (Nat.sub_add_cancel
          (two_mul_le_of_lhDomain (⟨k, h⟩ : Fin (lhDomainCard r n))))
        (cup (pull π (n - 2 * k) (d ⟨k, h⟩)) (cupPowE ξ k)) :=
  dif_pos h

theorem lhTermCard_of_ge (π : P ⟶ X) (ξ : Hmod2 P 2) (r n : ℕ)
    (d : (i : Fin (lhDomainCard r n)) → Hmod2 X (n - 2 * (i : ℕ))) {k : ℕ}
    (h : ¬ k < lhDomainCard r n) : lhTermCard π ξ r n d k = 0 :=
  dif_neg h

theorem lhMap_eq_sum_range (π : P ⟶ X) (ξ : Hmod2 P 2) (r n : ℕ)
    (d : (i : Fin (lhDomainCard r n)) → Hmod2 X (n - 2 * (i : ℕ))) :
    lhMap π ξ r n d
      = ∑ k ∈ Finset.range (lhDomainCard r n), lhTermCard π ξ r n d k := by
  rw [← Fin.sum_univ_eq_sum_range]
  unfold lhMap
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [lhTermCard_of_lt π ξ r n d i.2]

theorem lhSum_lhExtend_eq_sum_range (π : P ⟶ X) (ξ : Hmod2 P 2) (r n : ℕ)
    (d : (i : Fin (lhDomainCard r n)) → Hmod2 X (n - 2 * (i : ℕ))) :
    lhSum π ξ r n (lhExtend X r n d)
      = ∑ k ∈ Finset.range r, lhTermCard π ξ r n d k := by
  rw [lhSum_apply, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : (j : ℕ) < lhDomainCard r n
  · rw [lhTerm_of_le π ξ
      (two_mul_le_of_lhDomain (⟨(j : ℕ), h⟩ : Fin (lhDomainCard r n))),
      lhExtend_apply_of_lt X r n d h, lhTermCard_of_lt π ξ r n d h]
  · rw [lhExtend_apply_of_ge X r n d h, lhTerm_zero, lhTermCard_of_ge π ξ r n d h]

/-- **The two Leray–Hirsch combinations agree** along the extension by zero. -/
theorem lhMap_eq_lhSum (π : P ⟶ X) (ξ : Hmod2 P 2) (r n : ℕ)
    (d : (i : Fin (lhDomainCard r n)) → Hmod2 X (n - 2 * (i : ℕ))) :
    lhMap π ξ r n d = lhSum π ξ r n (lhExtend X r n d) := by
  rw [lhMap_eq_sum_range, lhSum_lhExtend_eq_sum_range]
  refine Finset.sum_subset
    (fun k hk => Finset.mem_range.mpr
      (lt_of_lt_of_le (Finset.mem_range.mp hk) (lhDomainCard_le r n))) ?_
  intro k _ hk
  exact lhTermCard_of_ge π ξ r n d fun hc => hk (Finset.mem_range.mpr hc)

/-! ## 3. Transfer -/

theorem bijective_of_comp_right {A B C : Type*} (g : B → C) (f : A → B)
    (hgf : Function.Bijective (g ∘ f)) (hf : Function.Bijective f) :
    Function.Bijective g := by
  constructor
  · intro x y hxy
    obtain ⟨a, rfl⟩ := hf.2 x
    obtain ⟨b, rfl⟩ := hf.2 y
    exact congrArg f (hgf.1 hxy)
  · intro z
    obtain ⟨a, ha⟩ := hgf.2 z
    exact ⟨f a, ha⟩

theorem lhMap_eq_comp (π : P ⟶ X) (ξ : Hmod2 P 2) (r n : ℕ) :
    lhMap π ξ r n = (fun c => lhSum π ξ r n c) ∘ lhExtend X r n :=
  funext fun d => lhMap_eq_lhSum π ξ r n d

theorem bijective_lhMap_of_lhSum (π : P ⟶ X) (ξ : Hmod2 P 2) (r n : ℕ)
    (h : Function.Bijective (lhSum π ξ r n)) :
    Function.Bijective (lhMap π ξ r n) := by
  rw [lhMap_eq_comp]
  exact Function.Bijective.comp h (bijective_lhExtend X r n)

theorem bijective_lhSum_of_lhMap (π : P ⟶ X) (ξ : Hmod2 P 2) (r n : ℕ)
    (h : Function.Bijective (lhMap π ξ r n)) :
    Function.Bijective (lhSum π ξ r n) := by
  rw [lhMap_eq_comp] at h
  exact bijective_of_comp_right _ _ h (bijective_lhExtend X r n)

/-- **The ladder's output, in the published interface.** -/
theorem lerayHirschGraded_of_bijective (π : P ⟶ X) (ξ : Hmod2 P 2) (r : ℕ)
    (h : ∀ n : ℕ, Function.Bijective (lhSum π ξ r n)) :
    LerayHirschGraded π ξ r :=
  ⟨fun n => bijective_lhMap_of_lhSum π ξ r n (h n)⟩

/-- The interface, back in the ladder's coordinates. -/
theorem bijective_lhSum_of_graded {π : P ⟶ X} {ξ : Hmod2 P 2} {r : ℕ}
    (L : LerayHirschGraded π ξ r) (n : ℕ) : Function.Bijective (lhSum π ξ r n) :=
  bijective_lhSum_of_lhMap π ξ r n (L.bij n)

end

end LH
end CharClass
end GroupApproximation
