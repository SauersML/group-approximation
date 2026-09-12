import GroupApproximation.GGT.GeodesicChainExists

/-!
# A geodesic chain through a prescribed between-point

`exists_isGeodesicChain` joins two points by a chain, but says nothing about
where the chain goes.  The slimness argument needs more: it is handed a point
`p` *between* `x` and `y` and has to compare it with a path, and the comparison
runs through chain vertices.  So `p` has to be one.

It can be, and cheaply: betweenness is exactly the statement that going through
`p` wastes nothing, so a chain from `x` to `p` followed by one from `p` to `y` is
again geodesic.  This module glues them.

## The three cases, and the `ite`

The glued chain is `fun i => if i ≤ j then c₁ i else c₂ (i - j)` with
`j = d(x,p)`.  Its geodesy splits into two easy cases --- both indices in one
piece --- and the straddling case, where the upper bound is the triangle
inequality through `p` and the lower bound is the triangle inequality from `x`
to `y` through both indices, using that `d(x,y)` is exactly `j + m`.

`omega` does not look inside an `ite`, so each case rewrites with `if_pos` or
`if_neg` first and only then reasons.
-/

namespace GroupApproximation
namespace GGT

open GroupApproximation.WordMetric

universe u

variable {G : Type u} [Group G]

/-- **A chain through a between-point.**

`p` lies between `x` and `y`, and the chain produced meets it at index
`d(x,p)`. -/
theorem exists_isGeodesicChain_through {S : Set G}
    (hS : IsSymmetricGeneratingSet S) {x p y : G}
    (hbet : Hyperbolic.IsBetween S x p y) :
    ∃ c : ℕ → G, c 0 = x ∧ c (wordDist S x y) = y ∧
      IsGeodesicChain S c (wordDist S x y) ∧ c (wordDist S x p) = p := by
  obtain ⟨c₁, hc₁0, hc₁j, h₁⟩ := exists_isGeodesicChain hS x p
  obtain ⟨c₂, hc₂0, hc₂m, h₂⟩ := exists_isGeodesicChain hS p y
  obtain ⟨j, hj⟩ : ∃ j : ℕ, j = wordDist S x p := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = wordDist S p y := ⟨_, rfl⟩
  have hsum : j + m = wordDist S x y := by
    have h : wordDist S x p + wordDist S p y = wordDist S x y := hbet
    omega
  rw [← hj] at hc₁j h₁
  rw [← hm] at hc₂m h₂
  -- the two endpoint readings of each piece
  have hxi : ∀ i : ℕ, i ≤ j → wordDist S x (c₁ i) = i := by
    intro i hi
    have h := h₁ 0 i (Nat.zero_le i) hi
    rw [hc₁0] at h
    omega
  have hiy : ∀ i : ℕ, i ≤ m → wordDist S (c₂ i) y = m - i := by
    intro i hi
    have h := h₂ i m hi le_rfl
    rw [hc₂m] at h
    exact h
  refine ⟨fun i => if i ≤ j then c₁ i else c₂ (i - j), ?_, ?_, ?_, ?_⟩
  · show (if (0 : ℕ) ≤ j then c₁ 0 else c₂ (0 - j)) = x
    rw [if_pos (Nat.zero_le j), hc₁0]
  · show (if wordDist S x y ≤ j then c₁ (wordDist S x y)
      else c₂ (wordDist S x y - j)) = y
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · have hjy : wordDist S x y = j := by omega
      rw [hjy, if_pos le_rfl, hc₁j]
      have hpy : c₂ 0 = y := by
        rw [← hc₂m, hm0]
      rw [← hc₂0, hpy]
    · rw [if_neg (by omega)]
      have hidx : wordDist S x y - j = m := by omega
      rw [hidx, hc₂m]
  · intro i k hik hkn
    show wordDist S (if i ≤ j then c₁ i else c₂ (i - j))
      (if k ≤ j then c₁ k else c₂ (k - j)) = k - i
    rcases (Nat.lt_or_ge j k).symm with hkj | hkj
    · rw [if_pos (le_trans hik hkj), if_pos hkj]
      exact h₁ i k hik hkj
    · rcases (Nat.lt_or_ge j i).symm with hij | hij
      · rw [if_pos hij, if_neg (by omega)]
        have hup : wordDist S (c₁ i) (c₂ (k - j)) ≤ j - i + (k - j) := by
          have h1 : wordDist S (c₁ i) p = j - i := by
            rw [← hc₁j]
            exact h₁ i j hij le_rfl
          have h2 : wordDist S p (c₂ (k - j)) = k - j := by
            rw [← hc₂0]
            have h := h₂ 0 (k - j) (Nat.zero_le _) (by omega)
            omega
          have htri := wordDist_triangle hS (c₁ i) p (c₂ (k - j))
          omega
        have h3 := hxi i hij
        have h4 := hiy (k - j) (by omega)
        have t1 := wordDist_triangle hS x (c₁ i) y
        have t2 := wordDist_triangle hS (c₁ i) (c₂ (k - j)) y
        omega
      · rw [if_neg (by omega), if_neg (by omega)]
        have h := h₂ (i - j) (k - j) (by omega) (by omega)
        omega
  · show (if wordDist S x p ≤ j then c₁ (wordDist S x p)
      else c₂ (wordDist S x p - j)) = p
    rw [← hj, if_pos le_rfl, hc₁j]

end GGT
end GroupApproximation
