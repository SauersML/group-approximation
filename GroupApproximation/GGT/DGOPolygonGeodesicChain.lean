import GroupApproximation.GGT.DGOThinPolygonVertex
import GroupApproximation.GGT.OsinTheorem54SepFourGonPinning
import GroupApproximation.GGT.OsinTheorem54SepPolygonVertex

/-!
# The sides of a `(1,0)`-quasi-geodesic polygon are geodesic chains

`GGT/DGOThinPolygonVertex.lean` proves thinness for `IsGeodesicChain`, an
indexed family of vertices whose word distance is the gap between the indices.
`OsinComponents.IsQuasiGeodesicPolygon` cuts a closed admissible word into sides
by a monotone `c` and asks each side for the lower bound
`(j - i)/μ - b ≤ d(vertex i, vertex j)`.  At `μ = 1`, `b = 0` that lower bound
is `j - i ≤ d`, and the matching upper bound `d ≤ j - i` holds for *any* word,
consecutive vertices being one letter apart.  So a side is a geodesic chain,
and this module is that observation.

The upper bound is osin-ah4's `wordDist_vertex_le`, stated at the basepoint `1`;
`wordDist_vertex_le'` moves it to an arbitrary basepoint by left invariance of
the word metric, `vertex_eq_mul_vertex_one` supplying the translation.

## What this is for

Dahmani--Guirardel--Osin's Lemma 4.16 needs their Lemma 4.15 --- thinness --- for
the polygon it is given.  Composing this with
`exists_index_wordDist_le_of_quadrangle` turns the polygon's own quasi-geodesic
clause into "every vertex of one side is within `10δ` of a vertex of another",
which is the form the corner-offset selection consumes: it must land on a
*vertex of a side*, since the cycle it assembles is made of segments of sides
and their safety comes from the distinguished component being isolated in the
polygon those segments came from.

The restriction to `μ = 1`, `b = 0` is the honest one.  For `b > 0` a side is
only a quasi-geodesic chain and the constant is Morse's;
`ElementaryMorseChord.exists_bound_chord_near_chain` proves exactly that, with
the same progress form `l · (j - i) - B ≤ d(y i, y j)`, but over `ℝ` and against
an `IsGeodesicSegment` chord, which the vertex model of `Γ(G, X ⊔ ℋ)` does not
carry.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **Two vertices of a word are at most their index gap apart**, from any
basepoint.  Left invariance of the word metric carries osin-ah4's
`wordDist_vertex_le` off the basepoint `1`. -/
theorem wordDist_vertex_le' (D : RelGenSet G Λ) {w : List (RelLetter G Λ)}
    (hlet : ∀ a ∈ w, D.IsLetter a) (v : G) {i j : ℕ} (hij : i ≤ j)
    (hj : j ≤ w.length) :
    wordDist D.alphabet.carrier (vertex v w i) (vertex v w j) ≤ j - i := by
  rw [vertex_eq_mul_vertex_one w v i, vertex_eq_mul_vertex_one w v j,
    wordDist_left_invariant]
  exact wordDist_vertex_le D hlet hij hj

/-- **Every side of a `(1,0)`-quasi-geodesic polygon is a geodesic chain.**

The cut points are returned with the chains, because the polygon predicate
carries them existentially and the corner-offset construction needs to name the
corners `vertex v w (c s)`. -/
theorem exists_geodesicChain_of_isQuasiGeodesicPolygon (D : RelGenSet G Λ)
    {n : ℕ} {v : G} {w : List (RelLetter G Λ)}
    (hP : IsQuasiGeodesicPolygon D 1 0 n v w) :
    ∃ c : ℕ → ℕ, c 0 = 0 ∧ c n = w.length ∧ Monotone c ∧
      ∀ s : ℕ, s < n →
        IsGeodesicChain D.alphabet.carrier
          (fun t => vertex v w (c s + t)) (c (s + 1) - c s) := by
  obtain ⟨hlet, -, c, hc0, hcn, hmono, hqg⟩ := hP
  have hmonoc : Monotone c := monotone_nat_of_le_succ hmono
  refine ⟨c, hc0, hcn, hmonoc, ?_⟩
  intro s hs i j hij hjlen
  have hcs : c s ≤ c (s + 1) := hmono s
  have hub : c (s + 1) ≤ w.length := by
    rw [← hcn]
    exact hmonoc (by omega : s + 1 ≤ n)
  have hjw : c s + j ≤ w.length := by omega
  show wordDist D.alphabet.carrier (vertex v w (c s + i)) (vertex v w (c s + j))
      = j - i
  have hupper := wordDist_vertex_le' D hlet v (by omega : c s + i ≤ c s + j) hjw
  have hlow := hqg s hs (c s + i) (c s + j) (by omega) (by omega) (by omega)
  rw [div_one, sub_zero] at hlow
  have hlower : c s + j - (c s + i)
      ≤ wordDist D.alphabet.carrier (vertex v w (c s + i))
          (vertex v w (c s + j)) := by
    exact_mod_cast hlow
  omega

end OsinComponents
end GGT
end GroupApproximation
