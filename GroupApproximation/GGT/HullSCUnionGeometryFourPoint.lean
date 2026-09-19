import GroupApproximation.GGT.HullSCUnionGeometryNormalForm
import GroupApproximation.Algebra.HyperbolicGroup

/-!
# The Cayley graph of a free product over a union alphabet is hyperbolic

Give each factor `G i` of a free product a symmetric generating set `S i`
satisfying Gromov's four-point condition at one common constant `δ`, and give
`CoprodI G` the union alphabet of `Algebra/FreeProductUnionNorm.lean`.  Then the
word metric of the union alphabet satisfies the four-point condition at the
*same* `δ`: `isFourPointHyperbolic_unionCarrier`.

This is the hyperbolicity half of `HullSC.FreeProductUnionGeometryStatement` ---
Hull's alphabet on `E ∗ H` can be taken to be the union of Hull's alphabets on
the factors --- and it is also the combinatorial statement that
`GGT.RelHyp.FreeProductConedFourPointStatement` isolates for Osin's Theorem
2.34, since the relative generating set `X ∪ U` is this alphabet with the
peripheral `S i` taken to be the whole factor.

## Why no constant is lost

The four-point condition is a statement about three Gromov products at a common
basepoint, and the word metric is left invariant, so the basepoint may be taken
to be `1`, where the normal form lives; `isFourPointHyperbolic_unionCarrier_aux`
is that reduction.  At `1` the three products are read off the leading syllables
of the three normal forms, by the three lemmas of
`GGT/HullSCUnionGeometryNormalForm.lean`, and the case analysis is on how the
three leading syllables branch:

* **all three agree** --- peel the common syllable.  Every distance is unchanged
  and every length drops by the same amount, so the inequality is literally the
  inequality for the three tails.  This is the only case that recurses, and it
  is why the induction is on the number of syllables of `x`.
* **`x` and `y` agree, or `y` and `z` agree** --- the two pairs that branch,
  branch the same way, so two applications of one branch lemma turn the
  inequality into an *equality* between its left side and one of the two terms
  of the `max`.  No `δ` is spent.
* **`x` and `z` agree** --- at least their common leading syllable cancels in
  `x⁻¹z`, and what is left is paid for by the triangle inequality inside the
  factor that `y` also branches in.  Again no `δ`.
* **all three differ** --- if any two of them lie in different factors, that
  pair contributes nothing and the corresponding term of the `max` already
  dominates.  Otherwise all three leading syllables `u`, `v`, `w` lie in one
  factor `F`, all three products are the factor's own products, and the
  inequality is exactly the factor's four-point condition at the quadruple
  `(1, v, u, w)`.

So the constant of the union is the constant of the factors: the tree directions
of a free product are `0`-hyperbolic and cost nothing.
-/

namespace GroupApproximation
namespace HullSCUnionGeometry

open Monoid Monoid.CoprodI
open GroupApproximation.WordMetric
open GroupApproximation.FreeProductCyclic
open GroupApproximation.FreeProductUnionNorm

section Main

variable {ι : Type*} [DecidableEq ι] {G : ι → Type*} [∀ i, Group (G i)]
  [∀ i, DecidableEq (G i)] {S : ∀ i, Set (G i)}

omit [DecidableEq ι] [(i : ι) → DecidableEq (G i)] in
/-- **The four-point inequality when the leading point is trivial.**  With
`x = 1` the left side is `|y| + |z|`, which is the second term of the `max`
exactly. -/
theorem fourPoint_one {δ : ℕ} (y z : CoprodI G) :
    wordNorm (unionCarrier S) y + wordNorm (unionCarrier S) ((1 : CoprodI G)⁻¹ * z)
      ≤ max (wordNorm (unionCarrier S) (1 : CoprodI G)
              + wordNorm (unionCarrier S) (y⁻¹ * z))
            (wordNorm (unionCarrier S) z
              + wordNorm (unionCarrier S) ((1 : CoprodI G)⁻¹ * y)) + 2 * δ := by
  rw [inv_one, one_mul, one_mul, wordNorm_one]
  refine le_trans ?_ (Nat.add_le_add_right (le_max_right _ _) (2 * δ))
  omega

/-- **The four-point condition at the basepoint `1`, by induction on the number
of syllables of `x`.**

The statement is the four-point inequality of the quadruple `(1, y, x, z)`,
which is the form in which the three Gromov products at `1` appear.  The
induction peels a syllable common to all three normal forms; every other
configuration of the three leading syllables is settled outright by the branch
lemmas of `GGT/HullSCUnionGeometryNormalForm.lean` together with the factors'
own four-point condition. -/
theorem fourPoint_aux (hS : ∀ i, IsSymmetricGeneratingSet (S i)) {δ : ℕ}
    (hδ : ∀ i, Hyperbolic.IsFourPointHyperbolic (S i) δ) :
    ∀ (n : ℕ) (x y z : CoprodI G), (Word.equiv x).toList.length ≤ n →
      wordNorm (unionCarrier S) y + wordNorm (unionCarrier S) (x⁻¹ * z)
        ≤ max (wordNorm (unionCarrier S) x + wordNorm (unionCarrier S) (y⁻¹ * z))
              (wordNorm (unionCarrier S) z + wordNorm (unionCarrier S) (x⁻¹ * y))
            + 2 * δ := by
  intro n
  induction n with
  | zero =>
      intro x y z hlen
      have hx1 : x = 1 := by
        refine sylLength_eq_zero_iff.mp ?_
        have h0 : (Word.equiv x).toList.length = 0 := Nat.le_zero.mp hlen
        simpa [sylLength] using h0
      rw [hx1]
      exact fourPoint_one y z
  | succ n ih =>
      intro x y z hlen
      rcases hx0 : lead x with _ | ⟨i, u⟩
      · rw [lead_eq_none_iff.mp hx0]
        exact fourPoint_one y z
      · have hfx : Word.fstIdx (Word.equiv x) = some i := fstIdx_of_lead_some hx0
        by_cases hxy : lead x = lead y
        · have hy0 : lead y = some ⟨i, u⟩ := hxy.symm.trans hx0
          have hfy : Word.fstIdx (Word.equiv y) = some i := fstIdx_of_lead_some hy0
          by_cases hyz : lead y = lead z
          · -- All three leading syllables agree: peel one syllable and recurse.
            have hz0 : lead z = some ⟨i, u⟩ := hyz.symm.trans hy0
            obtain ⟨x', hxeq, -, -, hxlen, hxnorm⟩ := exists_split hS hx0
            obtain ⟨y', hyeq, -, -, -, hynorm⟩ := exists_split hS hy0
            obtain ⟨z', hzeq, -, -, -, hznorm⟩ := exists_split hS hz0
            have e1 : x⁻¹ * z = x'⁻¹ * z' := by
              rw [hxeq, hzeq, mul_inv_rev, mul_assoc, inv_mul_cancel_left]
            have e2 : y⁻¹ * z = y'⁻¹ * z' := by
              rw [hyeq, hzeq, mul_inv_rev, mul_assoc, inv_mul_cancel_left]
            have e3 : x⁻¹ * y = x'⁻¹ * y' := by
              rw [hxeq, hyeq, mul_inv_rev, mul_assoc, inv_mul_cancel_left]
            have hih := ih x' y' z' (by omega)
            rw [e1, e2, e3, hxnorm, hynorm, hznorm]
            rcases le_total (wordNorm (unionCarrier S) x'
                  + wordNorm (unionCarrier S) (y'⁻¹ * z'))
                (wordNorm (unionCarrier S) z'
                  + wordNorm (unionCarrier S) (x'⁻¹ * y')) with hm | hm
            · rw [max_eq_right hm] at hih
              refine le_trans ?_ (Nat.add_le_add_right (le_max_right _ _) (2 * δ))
              omega
            · rw [max_eq_left hm] at hih
              refine le_trans ?_ (Nat.add_le_add_right (le_max_left _ _) (2 * δ))
              omega
          · -- `x` and `y` agree and `z` branches: the two pairs `(x,z)` and
            -- `(y,z)` branch alike, and the left term of the `max` is reached
            -- with equality.
            refine le_trans ?_ (Nat.add_le_add_right (le_max_left _ _) (2 * δ))
            by_cases hfz : Word.fstIdx (Word.equiv z) = some i
            · obtain ⟨w, hz0⟩ := exists_lead_index hfz
              have huw : u ≠ w := fun h => hyz (by rw [hy0, hz0, h])
              have p1 := wordNorm_branch_same hS hx0 hz0 huw
              have p2 := wordNorm_branch_same hS hy0 hz0 huw
              omega
            · have p1 : wordNorm (unionCarrier S) (x⁻¹ * z)
                  = wordNorm (unionCarrier S) x + wordNorm (unionCarrier S) z :=
                wordNorm_branch hS (by rw [hfx]; exact fun h => hfz h.symm)
              have p2 : wordNorm (unionCarrier S) (y⁻¹ * z)
                  = wordNorm (unionCarrier S) y + wordNorm (unionCarrier S) z :=
                wordNorm_branch hS (by rw [hfy]; exact fun h => hfz h.symm)
              omega
        · by_cases hyz : lead y = lead z
          · -- `y` and `z` agree and `x` branches: the right term of the `max`
            -- is reached with equality.
            refine le_trans ?_ (Nat.add_le_add_right (le_max_right _ _) (2 * δ))
            by_cases hfy : Word.fstIdx (Word.equiv y) = some i
            · obtain ⟨v, hy0⟩ := exists_lead_index hfy
              have hz0 : lead z = some ⟨i, v⟩ := hyz.symm.trans hy0
              have huv : u ≠ v := fun h => hxy (by rw [hx0, hy0, h])
              have q1 := wordNorm_branch_same hS hx0 hy0 huv
              have q2 := wordNorm_branch_same hS hx0 hz0 huv
              omega
            · have hbr : Word.fstIdx (Word.equiv x) ≠ Word.fstIdx (Word.equiv y) := by
                rw [hfx]
                exact fun h => hfy h.symm
              have q1 : wordNorm (unionCarrier S) (x⁻¹ * y)
                  = wordNorm (unionCarrier S) x + wordNorm (unionCarrier S) y :=
                wordNorm_branch hS hbr
              have q2 : wordNorm (unionCarrier S) (x⁻¹ * z)
                  = wordNorm (unionCarrier S) x + wordNorm (unionCarrier S) z :=
                wordNorm_branch hS (by rw [← fstIdx_congr hyz]; exact hbr)
              omega
          · by_cases hxz : lead x = lead z
            · -- `x` and `z` agree and `y` branches: their common leading
              -- syllable cancels in `x⁻¹z`, and the triangle inequality in the
              -- branching factor covers the rest.
              have hz0 : lead z = some ⟨i, u⟩ := hxz.symm.trans hx0
              have p3 := wordNorm_same_lead hS hx0 hz0
              refine le_trans ?_ (Nat.add_le_add_right (le_max_right _ _) (2 * δ))
              by_cases hfy : Word.fstIdx (Word.equiv y) = some i
              · obtain ⟨v, hy0⟩ := exists_lead_index hfy
                have huv : u ≠ v := fun h => hxy (by rw [hx0, hy0, h])
                have q1 := wordNorm_branch_same hS hx0 hy0 huv
                have htri : wordNorm (S i) v
                    ≤ wordNorm (S i) u + wordNorm (S i) (u⁻¹ * v) := by
                  have h := wordNorm_mul_le (hS i) u (u⁻¹ * v)
                  rwa [mul_inv_cancel_left] at h
                omega
              · have q1 : wordNorm (unionCarrier S) (x⁻¹ * y)
                    = wordNorm (unionCarrier S) x + wordNorm (unionCarrier S) y :=
                  wordNorm_branch hS (by rw [hfx]; exact fun h => hfy h.symm)
                omega
            · -- The three leading syllables are pairwise distinct.
              by_cases hfy : Word.fstIdx (Word.equiv y) = some i
              · obtain ⟨v, hy0⟩ := exists_lead_index hfy
                by_cases hfz : Word.fstIdx (Word.equiv z) = some i
                · -- All three leading syllables lie in the factor `i`: this is
                  -- the factor's own four-point condition at `(1, v, u, w)`.
                  obtain ⟨w, hz0⟩ := exists_lead_index hfz
                  have huv : u ≠ v := fun h => hxy (by rw [hx0, hy0, h])
                  have hvw : v ≠ w := fun h => hyz (by rw [hy0, hz0, h])
                  have huw : u ≠ w := fun h => hxz (by rw [hx0, hz0, h])
                  have q1 := wordNorm_branch_same hS hx0 hy0 huv
                  have q2 := wordNorm_branch_same hS hy0 hz0 hvw
                  have q3 := wordNorm_branch_same hS hx0 hz0 huw
                  have hf := hδ i 1 v u w
                  rw [wordDist_one_left, wordDist_one_left, wordDist_one_left] at hf
                  have hduw : wordDist (S i) u w = wordNorm (S i) (u⁻¹ * w) := rfl
                  have hdvw : wordDist (S i) v w = wordNorm (S i) (v⁻¹ * w) := rfl
                  have hdvu : wordDist (S i) v u = wordNorm (S i) (u⁻¹ * v) :=
                    wordDist_comm (hS i) v u
                  rw [hduw, hdvw, hdvu] at hf
                  rcases le_total (wordNorm (S i) u + wordNorm (S i) (v⁻¹ * w))
                      (wordNorm (S i) w + wordNorm (S i) (u⁻¹ * v)) with hm | hm
                  · rw [max_eq_right hm] at hf
                    refine le_trans ?_
                      (Nat.add_le_add_right (le_max_right _ _) (2 * δ))
                    omega
                  · rw [max_eq_left hm] at hf
                    refine le_trans ?_
                      (Nat.add_le_add_right (le_max_left _ _) (2 * δ))
                    omega
                · refine le_trans ?_ (Nat.add_le_add_right (le_max_left _ _) (2 * δ))
                  have q2 : wordNorm (unionCarrier S) (y⁻¹ * z)
                      = wordNorm (unionCarrier S) y + wordNorm (unionCarrier S) z :=
                    wordNorm_branch hS (by rw [hfy]; exact fun h => hfz h.symm)
                  have hsub := wordNorm_inv_mul_le
                    (isSymmetricGeneratingSet_unionCarrier hS) x z
                  omega
              · refine le_trans ?_ (Nat.add_le_add_right (le_max_right _ _) (2 * δ))
                have q1 : wordNorm (unionCarrier S) (x⁻¹ * y)
                    = wordNorm (unionCarrier S) x + wordNorm (unionCarrier S) y :=
                  wordNorm_branch hS (by rw [hfx]; exact fun h => hfy h.symm)
                have hsub := wordNorm_inv_mul_le
                  (isSymmetricGeneratingSet_unionCarrier hS) x z
                omega

/-- **The union alphabet of a free product is hyperbolic at the constant of its
factors.**

If every factor alphabet `S i` is symmetric and generating and satisfies
Gromov's four-point condition at `δ`, then so does the alphabet of `CoprodI G`
whose letters are the letters of every `S i` inside its own factor.  No constant
is lost, and no finiteness of any kind is used: the factor alphabets may be
infinite, as Hull's are, and so may the index type.

This is the hyperbolicity clause of `HullSC.FreeProductUnionGeometryStatement`,
at `CoprodI` generality.  The word metric is left invariant, so the four points
may be translated to put the first at the identity, which is
`fourPoint_aux`. -/
theorem isFourPointHyperbolic_unionCarrier
    (hS : ∀ i, IsSymmetricGeneratingSet (S i)) {δ : ℕ}
    (hδ : ∀ i, Hyperbolic.IsFourPointHyperbolic (S i) δ) :
    Hyperbolic.IsFourPointHyperbolic (unionCarrier S) δ := by
  intro w x y z
  have hC := isSymmetricGeneratingSet_unionCarrier hS
  show wordNorm (unionCarrier S) (w⁻¹ * x) + wordNorm (unionCarrier S) (y⁻¹ * z)
      ≤ max (wordNorm (unionCarrier S) (w⁻¹ * y)
              + wordNorm (unionCarrier S) (x⁻¹ * z))
            (wordNorm (unionCarrier S) (w⁻¹ * z)
              + wordNorm (unionCarrier S) (x⁻¹ * y)) + 2 * δ
  have key := fourPoint_aux hS hδ (Word.equiv (w⁻¹ * y)).toList.length
    (w⁻¹ * y) (w⁻¹ * x) (w⁻¹ * z) le_rfl
  have e0 : (w⁻¹ * y)⁻¹ * (w⁻¹ * z) = y⁻¹ * z := by group
  have e1 : (w⁻¹ * x)⁻¹ * (w⁻¹ * z) = x⁻¹ * z := by group
  have e2 : (w⁻¹ * y)⁻¹ * (w⁻¹ * x) = y⁻¹ * x := by group
  rw [e0, e1, e2] at key
  have hyx : wordNorm (unionCarrier S) (y⁻¹ * x)
      = wordNorm (unionCarrier S) (x⁻¹ * y) := by
    have h : (y : CoprodI G)⁻¹ * x = (x⁻¹ * y)⁻¹ := by group
    rw [h, wordNorm_inv hC]
  rw [hyx] at key
  exact key

end Main

end HullSCUnionGeometry
end GroupApproximation
