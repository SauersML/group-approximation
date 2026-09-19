import GroupApproximation.GGT.OsinTheorem54SepRotatePolygon
import GroupApproximation.GGT.OsinTheorem54SepFourGonSide

/-!
# The quadrilateral's own cut function, and its rotation

`IsQuasiGeodesicPolygon` binds its cut function existentially, so a consumer
holding the packaged predicate cannot say where the corners are.  Every
consumer of the quadrilateral `p ++ q ++ r ++ revWord s` knows exactly where
they are --- at `0`, `|p|`, `|p|+|q|`, `|p|+|q|+|r|`, `|w|` --- and needs to
say so, because the second reading of the polygon starts at one of them.

So this module names that cut function and proves the two packaging results
over it: the quadrilateral is a polygon, and so is the quadrilateral turned
round at the corner between `q` and `r`.

## Why that corner

The consumer's second reading has to begin in the arc between the end of a
component of `q` and the start of a component of the reversed `s`, and the
corner `|p| + |q|` always lies there: a component of `q` ends at or before it,
and a component of the reversed `s` starts at or after `|p| + |q| + |r|`.  So
no rotation from inside a side is ever needed, the number of sides is unchanged,
and the rotated quadrilateral is a quadrilateral.

## The hypothesis is not the packaged predicate

`hqg` below is the quasi-geodesic clause AT this cut function, which is strictly
more than `IsQuasiGeodesicPolygon` says: the predicate promises some cut, this
promises the natural one.  That is what a consumer actually verifies --- its
four sides are quasi-geodesic --- and both packagings come out of it.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## The cut function -/

/-- **The corners of `p ++ q ++ r ++ revWord s`.**  Constant past the fourth,
so that monotonicity holds at every index and not only below `4`. -/
def fourGonCut (p q r s : List (RelLetter G Λ)) (v : ℕ) : ℕ :=
  if v = 0 then 0
  else if v = 1 then p.length
  else if v = 2 then p.length + q.length
  else if v = 3 then p.length + q.length + r.length
  else p.length + q.length + r.length + s.length

variable (p q r s : List (RelLetter G Λ))

omit [Group G] in
theorem fourGonCut_zero : fourGonCut p q r s 0 = 0 := rfl

omit [Group G] in
theorem fourGonCut_one : fourGonCut p q r s 1 = p.length := rfl

omit [Group G] in
theorem fourGonCut_two : fourGonCut p q r s 2 = p.length + q.length := rfl

omit [Group G] in
theorem fourGonCut_three :
    fourGonCut p q r s 3 = p.length + q.length + r.length := rfl

omit [Group G] in
theorem fourGonCut_four :
    fourGonCut p q r s 4 = p.length + q.length + r.length + s.length := rfl

omit [Group G] in
/-- Past the fourth corner the cut function is constant. -/
theorem fourGonCut_of_four_le {v : ℕ} (hv : 4 ≤ v) :
    fourGonCut p q r s v = p.length + q.length + r.length + s.length := by
  unfold fourGonCut
  rw [if_neg (by omega : ¬ v = 0), if_neg (by omega : ¬ v = 1),
    if_neg (by omega : ¬ v = 2), if_neg (by omega : ¬ v = 3)]

/-- The fourth corner is the end of the word. -/
theorem fourGonCut_four_length :
    fourGonCut p q r s 4 = (p ++ q ++ r ++ revWord s).length :=
  (fourGonCut_four p q r s).trans (length_fourGon p q r s).symm

omit [Group G] in
/-- The corners increase. -/
theorem fourGonCut_mono (v : ℕ) :
    fourGonCut p q r s v ≤ fourGonCut p q r s (v + 1) := by
  by_cases h0 : v = 0
  · subst h0
    show (0 : ℕ) ≤ p.length
    exact Nat.zero_le _
  · by_cases h1 : v = 1
    · subst h1
      show p.length ≤ p.length + q.length
      omega
    · by_cases h2 : v = 2
      · subst h2
        show p.length + q.length ≤ p.length + q.length + r.length
        omega
      · by_cases h3 : v = 3
        · subst h3
          show p.length + q.length + r.length
            ≤ p.length + q.length + r.length + s.length
          omega
        · exact le_of_eq
            ((fourGonCut_of_four_le p q r s (by omega : 4 ≤ v)).trans
              (fourGonCut_of_four_le p q r s (by omega : 4 ≤ v + 1)).symm)

/-! ## The quadrilateral closes -/

/-- **The closing relation says the quadrilateral is a closed path.** -/
theorem listVal_fourGon_eq_one
    (hclose : RelLetter.listVal s
      = RelLetter.listVal p * RelLetter.listVal q * RelLetter.listVal r) :
    RelLetter.listVal (p ++ q ++ r ++ revWord s) = 1 := by
  rw [listVal_append, listVal_append, listVal_append, listVal_revWord, hclose]
  group

/-! ## The two packagings -/

/-- **The quadrilateral is a quasi-geodesic `4`-gon**, over the clause at its
own corners. -/
theorem isQuasiGeodesicPolygon_fourGon (D : RelGenSet G Λ) {mu b : ℝ}
    (hlet : ∀ a ∈ p ++ q ++ r ++ revWord s, D.IsLetter a)
    (hclose : RelLetter.listVal s
      = RelLetter.listVal p * RelLetter.listVal q * RelLetter.listVal r)
    (hqg : ∀ v : ℕ, v < 4 → ∀ i j : ℕ, fourGonCut p q r s v ≤ i → i ≤ j →
      j ≤ fourGonCut p q r s (v + 1) →
      ((j - i : ℕ) : ℝ) / mu - b
        ≤ ((wordDist D.alphabet.carrier
            (vertex (1 : G) (p ++ q ++ r ++ revWord s) i)
            (vertex (1 : G) (p ++ q ++ r ++ revWord s) j) : ℕ) : ℝ)) :
    IsQuasiGeodesicPolygon D mu b 4 1 (p ++ q ++ r ++ revWord s) :=
  ⟨hlet, listVal_fourGon_eq_one p q r s hclose, fourGonCut p q r s,
    fourGonCut_zero p q r s, fourGonCut_four_length p q r s,
    fourGonCut_mono p q r s, hqg⟩

/-- **The quadrilateral turned round at the corner between `q` and `r` is a
quasi-geodesic `4`-gon**, read from the vertex there.

This is the second linearisation, as a theorem.  Nothing is assumed beyond what
the first one already needed. -/
theorem isQuasiGeodesicPolygon_fourGon_rot (D : RelGenSet G Λ) {mu b : ℝ}
    (hlet : ∀ a ∈ p ++ q ++ r ++ revWord s, D.IsLetter a)
    (hclose : RelLetter.listVal s
      = RelLetter.listVal p * RelLetter.listVal q * RelLetter.listVal r)
    (hqg : ∀ v : ℕ, v < 4 → ∀ i j : ℕ, fourGonCut p q r s v ≤ i → i ≤ j →
      j ≤ fourGonCut p q r s (v + 1) →
      ((j - i : ℕ) : ℝ) / mu - b
        ≤ ((wordDist D.alphabet.carrier
            (vertex (1 : G) (p ++ q ++ r ++ revWord s) i)
            (vertex (1 : G) (p ++ q ++ r ++ revWord s) j) : ℕ) : ℝ)) :
    IsQuasiGeodesicPolygon D mu b 4
      (vertex (1 : G) (p ++ q ++ r ++ revWord s) (p.length + q.length))
      (rotWord (p ++ q ++ r ++ revWord s) (p.length + q.length)) := by
  have hrot := isQuasiGeodesicPolygon_rotWord D (t := 2) hlet
    (listVal_fourGon_eq_one p q r s hclose) (fourGonCut_zero p q r s)
    (fourGonCut_four_length p q r s) (fourGonCut_mono p q r s)
    (by omega : (2 : ℕ) < 4) hqg
  rwa [fourGonCut_two] at hrot

end OsinComponents
end GGT
end GroupApproximation
