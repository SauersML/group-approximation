import GroupApproximation.GGT.DGOIsolatedComponentRotateCut

/-!
# A polygon turned round at a corner is a polygon

`DGOIsolatedComponentRotateCut.exists_rot_cut` carries the cut function of an
`N`-gon across a rotation at a corner, with one side exempted from the
quasi-geodesic clause --- the exemption its own consumer wants, the
distinguished side arriving at index `0`.  A consumer that has the clause at
EVERY side wants the packaged predicate back, and that is all this module does:
it hands `exists_rot_cut` the unexempted hypothesis and supplies the missing
clause at side `0`, which is the old side `t` read through
`vertex_rotWord_le`.

Nothing here is new geometry.  `rotWord`, the vertex identities, the cut
function and its monotonicity are all fp-geometry's; this is the wrapper that
turns them back into `IsQuasiGeodesicPolygon`.

## What this does not give

The rotation is at a CORNER, `c t` for a side index `t`, and the number of sides
is unchanged.  A rotation from a point strictly inside a side is not here; it
would go through a refinement of the cut function, of which
`DGOIsolatedComponentRecut` is the two-point case (an `n`-gon becomes an
`(n+2)`-gon with a prescribed interval as a side), and it would cost sides.

The quadrilateral application does not need it.  In `p ++ q ++ r ++ revWord s`
the second reading has to begin somewhere in the arc between the end of the
`q`-component and the start of the `s`-component, and that arc always contains
the corner `|p| + |q|`: the component of `q` ends at or before it, and the
component of the reversed `s` starts at or after `|p| + |q| + |r|`.  So the
corner case suffices there, and the rotated quadrilateral is a quadrilateral.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **The rotation of a quasi-geodesic `N`-gon at a corner is a quasi-geodesic
`N`-gon.**

The polygon is taken apart into its data rather than passed whole, because the
corner is named by the cut function, which the predicate binds existentially. -/
theorem isQuasiGeodesicPolygon_rotWord (D : RelGenSet G Λ) {mu b : ℝ}
    {N t : ℕ} {v : G} {w : List (RelLetter G Λ)} {c : ℕ → ℕ}
    (hlet : ∀ a ∈ w, D.IsLetter a) (hclosed : RelLetter.listVal w = 1)
    (hc0 : c 0 = 0) (hcN : c N = w.length) (hcmono : ∀ s : ℕ, c s ≤ c (s + 1))
    (ht : t < N)
    (hcqg : ∀ s : ℕ, s < N → ∀ p q : ℕ, c s ≤ p → p ≤ q → q ≤ c (s + 1) →
      ((q - p : ℕ) : ℝ) / mu - b
        ≤ ((wordDist D.alphabet.carrier (vertex v w p)
            (vertex v w q) : ℕ) : ℝ)) :
    IsQuasiGeodesicPolygon D mu b N (vertex v w (c t)) (rotWord w (c t)) := by
  obtain ⟨d, hd0, hd1, hdN, hdmono, hdqg⟩ :=
    exists_rot_cut D mu b hclosed hc0 hcN hcmono ht
      (fun s hs _ p q hp hpq hq => hcqg s hs p q hp hpq hq)
  refine ⟨letters_rotWord D hlet (c t), listVal_rotWord w (c t) hclosed,
    d, hd0, hdN, hdmono, ?_⟩
  intro s hs p q hp hpq hq
  by_cases hs0 : s = 0
  · -- the first side of the rotated polygon is the old side `t`
    subst hs0
    rw [hd1] at hq
    have hmono : Monotone c := monotone_nat_of_le_succ hcmono
    have hct : c t ≤ c (t + 1) := hcmono t
    have hct1 : c (t + 1) ≤ w.length := by
      have hle := hmono (show t + 1 ≤ N by omega)
      omega
    have hctw : c t ≤ w.length := by omega
    rw [vertex_rotWord_le v w hctw p (by omega),
      vertex_rotWord_le v w hctw q (by omega)]
    have hb := hcqg t ht (c t + p) (c t + q) (by omega) (by omega) (by omega)
    have hnum : c t + q - (c t + p) = q - p := by omega
    rw [hnum] at hb
    exact hb
  · exact hdqg s hs hs0 p q hp hpq hq

end OsinComponents
end GGT
end GroupApproximation
