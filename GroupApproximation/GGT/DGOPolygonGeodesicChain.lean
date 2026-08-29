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

## The corner offset lives here too

`notMem_coset_of_offset` and `notMem_coset_vertex_of_offset` are the selection
device of Lemma 4.16, and they are stated here because they need nothing but the
word metric and `wordDist_le_one_of_mem_fam`: a point of the coset `x · H lam`
is one alphabet letter from `x`, so choosing the offset point at distance
`θ + 2` from the corner puts the whole `θ`-ball around it outside the coset.
No thinness, no polygon and no hyperbolicity is used --- those are what supply
the offset point and bound the connector, not what makes the count work.
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

/-! ## The corner offset -/

/-- **The corner offset excludes the coset.**  If `u` is chosen at distance at
least `θ + 2` from a corner `x`, then nothing within `θ` of `u` lies in the coset
`x · H lam`: a point of that coset is joined to `x` by a single letter of the
alphabet, so it would put `x` within `1 + θ` of `u`.

This is the whole of Dahmani--Guirardel--Osin's device for making the connector
of their Lemma 4.16 usable, and it answers the question their proof is usually
read as begging.  The connector is a geodesic between two points of the polygon
and is **not** required to avoid `Γ_{H lam}`, nor are the thinness points
required to lie outside the coset.  What has to be excluded is only that some
component *of the connector* is connected to the distinguished component, and
the offset is chosen one unit above what such a connection would force. -/
theorem notMem_coset_of_offset (D : RelGenSet G Λ) {lam : Λ} {x u z : G}
    {θ : ℕ} (hoff : θ + 2 ≤ wordDist D.alphabet.carrier x u)
    (hz : wordDist D.alphabet.carrier u z ≤ θ) :
    x⁻¹ * z ∉ D.fam lam := by
  intro hmem
  have h1 : wordDist D.alphabet.carrier x z ≤ 1 :=
    wordDist_le_one_of_mem_fam D hmem
  have h2 := wordDist_triangle D.alphabet.symmetricGenerating x z u
  have h3 : wordDist D.alphabet.carrier z u = wordDist D.alphabet.carrier u z :=
    wordDist_comm D.alphabet.symmetricGenerating z u
  omega

/-- **No vertex of a short connector meets the coset of a distant corner.**  The
connector is read from `u` and its `m`-th vertex is at most `m` letters away, so
`notMem_coset_of_offset` applies to all of them at once.

Read against the cycle Lemma 4.16 assembles, this says that the only `lam`-letter
of the connector that could sit at a vertex of the distinguished component's
coset would have to sit at a vertex that is not there --- so the connector
contributes no component connected to the distinguished one, which is what
`OsinComponents.IsIsolated` asks of the assembled cycle. -/
theorem notMem_coset_vertex_of_offset (D : RelGenSet G Λ) {lam : Λ} {x u : G}
    {θ : ℕ} {r : List (RelLetter G Λ)} (hlet : ∀ a ∈ r, D.IsLetter a)
    (hlen : r.length ≤ θ)
    (hoff : θ + 2 ≤ wordDist D.alphabet.carrier x u)
    {m : ℕ} (hm : m ≤ r.length) :
    x⁻¹ * vertex u r m ∉ D.fam lam := by
  refine notMem_coset_of_offset D hoff ?_
  have h := wordDist_vertex_le' D hlet u (Nat.zero_le m) hm
  rw [vertex_zero] at h
  omega

end OsinComponents
end GGT
end GroupApproximation
