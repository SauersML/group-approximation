import GroupApproximation.Sofic.CliffordLampGroup
import Mathlib.Data.Finset.Sort
import GroupApproximation.Meta.AxiomGuard

/-!
# Splicing a point into a sorted Clifford lamp word

`Sofic/CliffordLampGroup.lean` proves that `toModel X : CliffordLamp X →* SignedModel X` is onto
but not that it is injective.  This module supplies the combinatorial half of the missing normal
form: `wordOfSupport s`, the product of the lamps at a finite subset `s` (sorted ascending), and
the exact identity for how that product changes when a fresh point `x ∉ s` is spliced into it at
its sorted position --- one central sign for every already-present point greater than `x`, since
inserting `lamp X x` there means commuting it leftward past each of them.

`Sofic/CliffordLampNormalForm.lean` uses `wordOfSupport_insert` to build the explicit section of
`toModel` and prove it bijective.
-/

namespace GroupApproximation
namespace CliffordLampNormalFormSplice

open CliffordLamp
open scoped commutatorElement

noncomputable section

variable {X : Type}

/-! ## Words -/

/-- The product of lamps at the entries of a list, in order. -/
def wordOfList (l : List X) : CliffordLamp X :=
  l.foldr (fun x acc => lamp X x * acc) 1

@[simp] theorem wordOfList_nil : (wordOfList (X := X) [] : CliffordLamp X) = 1 := rfl

@[simp] theorem wordOfList_cons (x : X) (l : List X) :
    wordOfList (x :: l) = lamp X x * wordOfList l := rfl

/-! ## Swapping a lamp past a word of other lamps -/

theorem lamp_sq_mul_self (x : X) : lamp X x * lamp X x = 1 := by
  simpa [pow_two] using lamp_sq X x

theorem lamp_inv_eq_self (x : X) : (lamp X x)⁻¹ = lamp X x :=
  inv_eq_of_mul_eq_one_left (lamp_sq_mul_self x)

/-- Distinct lamps swap past each other at the cost of one central sign. -/
theorem lamp_mul_lamp_swap {x y : X} (h : x ≠ y) :
    lamp X x * lamp X y = sign X * (lamp X y * lamp X x) := by
  have hc : lamp X x * lamp X y * lamp X x * lamp X y = sign X := by
    have h0 := commutator_lamp_lamp X h
    rwa [commutatorElement_def, lamp_inv_eq_self, lamp_inv_eq_self] at h0
  have hxx := lamp_sq_mul_self (X := X) x
  have hyy := lamp_sq_mul_self (X := X) y
  apply mul_right_cancel (b := lamp X x * lamp X y)
  calc lamp X x * lamp X y * (lamp X x * lamp X y)
      = lamp X x * lamp X y * lamp X x * lamp X y := by simp only [mul_assoc]
    _ = sign X := hc
    _ = sign X * (lamp X y * lamp X y) := by rw [hyy, mul_one]
    _ = sign X * (lamp X y * (lamp X x * lamp X x) * lamp X y) := by rw [hxx, mul_one]
    _ = sign X * (lamp X y * lamp X x) * (lamp X x * lamp X y) := by simp only [mul_assoc]

theorem wordOfList_append_cons (l₁ : List X) (y : X) (l₂ : List X) :
    wordOfList (l₁ ++ y :: l₂) = wordOfList l₁ * (lamp X y * wordOfList l₂) := by
  induction l₁ with
  | nil => simp
  | cons a as ih => simp only [List.cons_append, wordOfList_cons, ih, mul_assoc]

theorem wordOfList_append (l₁ l₂ : List X) :
    wordOfList (l₁ ++ l₂) = wordOfList l₁ * wordOfList l₂ := by
  induction l₁ with
  | nil => simp
  | cons a as ih => simp only [List.cons_append, wordOfList_cons, ih, mul_assoc]

/-- A word of lamps commutes past any power of the central sign. -/
theorem wordOfList_mul_sign_pow_comm (l : List X) (n : ℕ) :
    wordOfList l * sign X ^ n = sign X ^ n * wordOfList l := by
  induction l with
  | nil => simp
  | cons a as ih =>
      have hcomm : lamp X a * sign X ^ n = sign X ^ n * lamp X a :=
        ((sign_commute_lamp X a).symm.pow_right n).eq
      calc wordOfList (a :: as) * sign X ^ n
          = lamp X a * (wordOfList as * sign X ^ n) := by
            simp only [wordOfList_cons, mul_assoc]
        _ = lamp X a * (sign X ^ n * wordOfList as) := by rw [ih]
        _ = (lamp X a * sign X ^ n) * wordOfList as := by rw [mul_assoc]
        _ = (sign X ^ n * lamp X a) * wordOfList as := by rw [hcomm]
        _ = sign X ^ n * wordOfList (a :: as) := by simp only [wordOfList_cons, mul_assoc]

/-- A fresh lamp commutes past a word of other, distinct lamps, at the cost of one central sign
per letter. -/
theorem lamp_mul_wordOfList (x : X) (l : List X) (hx : x ∉ l) :
    lamp X x * wordOfList l = sign X ^ l.length * wordOfList l * lamp X x := by
  induction l with
  | nil => simp
  | cons y ys ih =>
      have hxy : x ≠ y := by
        intro h; apply hx; rw [h]; exact List.mem_cons_self
      have hxys : x ∉ ys := fun h ↦ hx (List.mem_cons_of_mem _ h)
      have hcomm : lamp X y * sign X ^ ys.length = sign X ^ ys.length * lamp X y :=
        ((sign_commute_lamp X y).symm.pow_right ys.length).eq
      calc lamp X x * wordOfList (y :: ys)
          = lamp X x * lamp X y * wordOfList ys := by simp only [wordOfList_cons, mul_assoc]
        _ = sign X * (lamp X y * lamp X x) * wordOfList ys := by
            rw [lamp_mul_lamp_swap hxy]
        _ = sign X * lamp X y * (lamp X x * wordOfList ys) := by simp only [mul_assoc]
        _ = sign X * lamp X y * (sign X ^ ys.length * wordOfList ys * lamp X x) := by
            rw [ih hxys]
        _ = sign X * (lamp X y * sign X ^ ys.length) * wordOfList ys * lamp X x := by
            simp only [mul_assoc]
        _ = sign X * (sign X ^ ys.length * lamp X y) * wordOfList ys * lamp X x := by
            rw [hcomm]
        _ = sign X ^ (ys.length + 1) * (lamp X y * wordOfList ys) * lamp X x := by
            rw [pow_succ']
            simp only [mul_assoc]
        _ = sign X ^ (y :: ys).length * wordOfList (y :: ys) * lamp X x := by
            rw [List.length_cons, wordOfList_cons]

variable [LinearOrder X]

/-! ## Words attached to finite sets -/

/-- The word attached to a finite subset: its elements, sorted ascending. -/
def wordOfSupport (s : Finset X) : CliffordLamp X := wordOfList (s.sort (· ≤ ·))

theorem wordOfSupport_def (s : Finset X) :
    wordOfSupport s = wordOfList (s.sort (· ≤ ·)) := rfl

@[simp] theorem wordOfSupport_empty : wordOfSupport (∅ : Finset X) = 1 := by
  simp [wordOfSupport_def]

/-! ## Splicing a point into a sorted word -/

/-- Splicing a fresh point `x` into the sorted word of `s` picks up one central sign for every
already-present point greater than `x`. -/
theorem wordOfSupport_insert {s : Finset X} {x : X} (hx : x ∉ s) :
    wordOfSupport (insert x s) =
      sign X ^ ((s.filter (x < ·)).card) * wordOfSupport s * lamp X x := by
  classical
  set smaller := s.filter (· < x) with hsmaller_def
  set bigger := s.filter (x < ·) with hbigger_def
  have hunion : smaller ∪ bigger = s := by
    ext y
    simp only [hsmaller_def, hbigger_def, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hy, _⟩ | ⟨hy, _⟩) <;> exact hy
    · intro hy
      rcases lt_trichotomy y x with hlt | heq | hgt
      · exact Or.inl ⟨hy, hlt⟩
      · rw [heq] at hy; exact absurd hy hx
      · exact Or.inr ⟨hy, hgt⟩
  have hdisj : Disjoint smaller bigger := by
    rw [Finset.disjoint_left]
    intro y hy1 hy2
    simp only [hsmaller_def, hbigger_def, Finset.mem_filter] at hy1 hy2
    exact absurd (hy1.2.trans hy2.2) (lt_irrefl y)
  have hxsmaller : x ∉ smaller := by
    simp only [hsmaller_def, Finset.mem_filter]
    exact fun h => absurd h.2 (lt_irrefl x)
  have hxbigger : x ∉ bigger := by
    simp only [hbigger_def, Finset.mem_filter]
    exact fun h => absurd h.2 (lt_irrefl x)
  set L : List X := smaller.sort (· ≤ ·) ++ x :: bigger.sort (· ≤ ·) with hL_def
  have hLnodup : L.Nodup := by
    rw [hL_def, List.nodup_append]
    refine ⟨Finset.sort_nodup _ _, ?_, ?_⟩
    · rw [List.nodup_cons]
      exact ⟨by simpa using hxbigger, Finset.sort_nodup _ _⟩
    · intro a ha b hb
      rw [Finset.mem_sort] at ha
      rw [List.mem_cons] at hb
      rcases hb with rfl | hb
      · intro h
        rw [h] at ha
        exact hxsmaller ha
      · rw [Finset.mem_sort] at hb
        intro h
        rw [h] at ha
        exact Finset.disjoint_left.mp hdisj ha hb
  have hLtoFinset : L.toFinset = insert x s := by
    rw [hL_def, List.toFinset_append, List.toFinset_cons]
    simp only [Finset.sort_toFinset]
    rw [← hunion]
    ext y
    simp only [Finset.mem_union, Finset.mem_insert]
    tauto
  have hLpairwise : L.Pairwise (· ≤ ·) := by
    rw [hL_def, List.pairwise_append]
    refine ⟨Finset.pairwise_sort _ _, ?_, ?_⟩
    · rw [List.pairwise_cons]
      refine ⟨?_, Finset.pairwise_sort _ _⟩
      intro b hb
      rw [Finset.mem_sort] at hb
      simp only [hbigger_def, Finset.mem_filter] at hb
      exact le_of_lt hb.2
    · intro a ha b hb
      rw [Finset.mem_sort] at ha
      simp only [hsmaller_def, Finset.mem_filter] at ha
      rw [List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact le_of_lt ha.2
      · rw [Finset.mem_sort] at hb
        simp only [hbigger_def, Finset.mem_filter] at hb
        exact le_of_lt (ha.2.trans hb.2)
  have hsort : (insert x s).sort (· ≤ ·) = L := by
    rw [← hLtoFinset]
    exact (List.toFinset_sort (· ≤ ·) hLnodup).mpr hLpairwise
  have hsort_s : s.sort (· ≤ ·) = smaller.sort (· ≤ ·) ++ bigger.sort (· ≤ ·) := by
    have hnodup' : (smaller.sort (· ≤ ·) ++ bigger.sort (· ≤ ·)).Nodup := by
      rw [List.nodup_append]
      refine ⟨Finset.sort_nodup _ _, Finset.sort_nodup _ _, ?_⟩
      intro a ha b hb
      rw [Finset.mem_sort] at ha hb
      intro h
      rw [h] at ha
      exact Finset.disjoint_left.mp hdisj ha hb
    have htoFinset' : (smaller.sort (· ≤ ·) ++ bigger.sort (· ≤ ·)).toFinset = s := by
      rw [List.toFinset_append]
      simp only [Finset.sort_toFinset]
      exact hunion
    have hpairwise' : (smaller.sort (· ≤ ·) ++ bigger.sort (· ≤ ·)).Pairwise (· ≤ ·) := by
      rw [List.pairwise_append]
      refine ⟨Finset.pairwise_sort _ _, Finset.pairwise_sort _ _, ?_⟩
      intro a ha b hb
      rw [Finset.mem_sort] at ha hb
      simp only [hsmaller_def, Finset.mem_filter] at ha
      simp only [hbigger_def, Finset.mem_filter] at hb
      exact le_of_lt (ha.2.trans hb.2)
    rw [← htoFinset']
    exact (List.toFinset_sort (· ≤ ·) hnodup').mpr hpairwise'
  calc wordOfSupport (insert x s)
      = wordOfList L := by rw [wordOfSupport_def, hsort]
    _ = wordOfList (smaller.sort (· ≤ ·)) * (lamp X x * wordOfList (bigger.sort (· ≤ ·))) := by
        rw [hL_def, wordOfList_append_cons]
    _ = wordOfList (smaller.sort (· ≤ ·)) *
          (sign X ^ (bigger.sort (· ≤ ·)).length * wordOfList (bigger.sort (· ≤ ·)) *
            lamp X x) := by
        rw [lamp_mul_wordOfList x (bigger.sort (· ≤ ·)) (by rw [Finset.mem_sort]; exact hxbigger)]
    _ = sign X ^ (bigger.sort (· ≤ ·)).length *
          (wordOfList (smaller.sort (· ≤ ·)) * wordOfList (bigger.sort (· ≤ ·))) *
          lamp X x := by
        have hswap := wordOfList_mul_sign_pow_comm (smaller.sort (· ≤ ·))
          (bigger.sort (· ≤ ·)).length
        calc wordOfList (smaller.sort (· ≤ ·)) *
              (sign X ^ (bigger.sort (· ≤ ·)).length * wordOfList (bigger.sort (· ≤ ·)) *
                lamp X x)
            = wordOfList (smaller.sort (· ≤ ·)) * sign X ^ (bigger.sort (· ≤ ·)).length *
                wordOfList (bigger.sort (· ≤ ·)) * lamp X x := by
              simp only [mul_assoc]
          _ = sign X ^ (bigger.sort (· ≤ ·)).length * wordOfList (smaller.sort (· ≤ ·)) *
                wordOfList (bigger.sort (· ≤ ·)) * lamp X x := by rw [hswap]
          _ = sign X ^ (bigger.sort (· ≤ ·)).length *
                (wordOfList (smaller.sort (· ≤ ·)) * wordOfList (bigger.sort (· ≤ ·))) *
                lamp X x := by simp only [mul_assoc]
    _ = sign X ^ ((s.filter (x < ·)).card) * wordOfSupport s * lamp X x := by
        rw [wordOfSupport_def, hsort_s, wordOfList_append, Finset.length_sort]

end
end CliffordLampNormalFormSplice
end GroupApproximation

open GroupApproximation
open GroupApproximation.CliffordLampNormalFormSplice

#audit_axioms lamp_mul_lamp_swap
#audit_axioms lamp_mul_wordOfList
#audit_axioms wordOfSupport_insert
