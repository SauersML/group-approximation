import GroupApproximation.Algebra.WordMetricComparison
import GroupApproximation.GGT.DGOThinPolygonVertex

/-!
# Every pair of points is joined by a geodesic chain

`GGT/DGOThinPolygonVertex.lean` defines `IsGeodesicChain` --- a map `ℕ → G`
whose vertices satisfy `d(c i, c j) = j - i` up to the length --- and proves that
its vertices lie between its endpoints.  Nothing in the tree *constructs* one:
the chains that occur there arrive as sides of polygons, already given.

An argument that has to subdivide a pair of points, rather than read a chain off
a polygon, needs the construction, so it gets its own module.  It is the list
model of a geodesic, exactly as `WordMetricComparison.IsGeodesicWord` is: the
chain is `i ↦ x · (prefix of length i)`, and the two bounds meet because
`wordNorm_prod_take` says initial segments of a geodesic word march out at unit
speed.

## The two bounds

The upper bound `d(c i, c j) ≤ j - i` is the triangle inequality along the unit
steps, and the unit steps are `List.prod_take_succ`: reading one more letter
multiplies by that letter, whose word norm is at most one.  Mathlib does not
state `l.take (i + m) = l.take i ++ (l.drop i).take m`, so the segment route
would need that lemma; the step-by-step induction avoids it.

The lower bound is `wordNorm_prod_take` against the triangle inequality from the
basepoint: `d(x, c j) = j` and `d(x, c i) = i` force `d(c i, c j) ≥ j - i`.
-/

namespace GroupApproximation
namespace GGT

open GroupApproximation.WordMetric

universe u

variable {G : Type u} [Group G]

/-- **Every pair of points is joined by a geodesic chain.**

The chain is indexed by `ℕ` and is only claimed to be geodesic up to
`wordDist S x y`; past that index it is the constant `y`, which is what the
`take` of an over-long prefix gives and is harmless, `IsGeodesicChain` saying
nothing there. -/
theorem exists_isGeodesicChain {S : Set G} (hS : IsSymmetricGeneratingSet S)
    (x y : G) :
    ∃ c : ℕ → G, c 0 = x ∧ c (wordDist S x y) = y ∧
      IsGeodesicChain S c (wordDist S x y) := by
  obtain ⟨l, hl⟩ := exists_isGeodesicWord hS (x⁻¹ * y)
  have hlen : l.length = wordDist S x y := hl.length_eq
  -- one letter at a time
  have hunit : ∀ k : ℕ, k < l.length →
      wordDist S (x * (l.take k).prod) (x * (l.take (k + 1)).prod) ≤ 1 := by
    intro k hk
    show wordNorm S
      ((x * (l.take k).prod)⁻¹ * (x * (l.take (k + 1)).prod)) ≤ 1
    rw [List.prod_take_succ l k hk]
    have hval : (x * (l.take k).prod)⁻¹ * (x * ((l.take k).prod * l[k]'hk))
        = l[k]'hk := by group
    rw [hval]
    exact wordNorm_le_one_of_mem (hl.isWord.letters _ (List.getElem_mem hk))
  -- the prefixes march out at unit speed
  have hnorm : ∀ k : ℕ, k ≤ l.length →
      wordDist S x (x * (l.take k).prod) = k := by
    intro k hk
    show wordNorm S (x⁻¹ * (x * (l.take k).prod)) = k
    rw [inv_mul_cancel_left, wordNorm_prod_take hS hl k]
    exact Hyperbolic.length_take_of_le hk
  -- the upper bound, by the triangle inequality along the unit steps
  have hup : ∀ j : ℕ, j ≤ l.length → ∀ i : ℕ, i ≤ j →
      wordDist S (x * (l.take i).prod) (x * (l.take j).prod) ≤ j - i := by
    intro j
    induction j with
    | zero =>
        intro _ i hi
        have hi0 : i = 0 := by omega
        subst hi0
        have h := wordDist_self S (x * (l.take 0).prod)
        omega
    | succ j ih =>
        intro hjn i hi
        rcases Nat.lt_or_ge i (j + 1) with hlt | hge
        · have h1 := ih (by omega) i (by omega)
          have h2 := hunit j (by omega)
          have htri := wordDist_triangle hS (x * (l.take i).prod)
            (x * (l.take j).prod) (x * (l.take (j + 1)).prod)
          omega
        · have hij : i = j + 1 := by omega
          subst hij
          have h := wordDist_self S (x * (l.take (j + 1)).prod)
          omega
  refine ⟨fun i => x * (l.take i).prod, ?_, ?_, ?_⟩
  · show x * (l.take 0).prod = x
    rw [List.take_zero, List.prod_nil, mul_one]
  · show x * (l.take (wordDist S x y)).prod = y
    rw [← hlen, List.take_length, hl.isWord.prod_eq, mul_inv_cancel_left]
  · intro i j hij hjn
    show wordDist S (x * (l.take i).prod) (x * (l.take j).prod) = j - i
    have h1 := hup j (by omega) i hij
    have h2 := hnorm i (by omega)
    have h3 := hnorm j (by omega)
    have htri := wordDist_triangle hS x (x * (l.take i).prod)
      (x * (l.take j).prod)
    omega

end GGT
end GroupApproximation
