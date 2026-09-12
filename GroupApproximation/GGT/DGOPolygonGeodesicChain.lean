import GroupApproximation.GGT.DGOThinPolygonVertex
import GroupApproximation.GGT.OsinTheorem54SepFourGonPinning
import GroupApproximation.GGT.OsinTheorem54SepPolygonVertex
import GroupApproximation.GGT.DGOIsolatedComponentBridge

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

/-- **Every side of a `(1,b)`-quasi-geodesic polygon is a `(1,b)`-quasi-geodesic
chain.**

The cut points are returned with the chains, because the polygon predicate
carries them existentially and the corner-offset construction needs to name the
corners `vertex v w (c s)`.

Both bounds of `IsQuasiGeodesicChain` are supplied here: the lower one is the
polygon's clause at `μ = 1`, the upper one is `wordDist_vertex_le'` and holds of
any word.  At `b = 0` this is the geodesic-chain statement, through
`IsQuasiGeodesicChain.isGeodesicChain`. -/
theorem exists_geodesicChain_of_isQuasiGeodesicPolygon (D : RelGenSet G Λ)
    {n b : ℕ} {v : G} {w : List (RelLetter G Λ)}
    (hP : IsQuasiGeodesicPolygon D 1 (b : ℝ) n v w) :
    ∃ c : ℕ → ℕ, c 0 = 0 ∧ c n = w.length ∧ Monotone c ∧
      ∀ s : ℕ, s < n →
        IsQuasiGeodesicChain D.alphabet.carrier b
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
  show (j - i) - b
      ≤ wordDist D.alphabet.carrier (vertex v w (c s + i))
        (vertex v w (c s + j)) ∧
      wordDist D.alphabet.carrier (vertex v w (c s + i))
        (vertex v w (c s + j)) ≤ j - i
  have hupper := wordDist_vertex_le' D hlet v (by omega : c s + i ≤ c s + j) hjw
  have hlow := hqg s hs (c s + i) (c s + j) (by omega) (by omega) (by omega)
  rw [div_one] at hlow
  -- the real clause `x - b ≤ d` is transported as the natural `x ≤ d + b`, the
  -- shape truncated subtraction is recovered from
  have hlow' : ((c s + j - (c s + i) : ℕ) : ℝ)
      ≤ ((wordDist D.alphabet.carrier (vertex v w (c s + i))
        (vertex v w (c s + j)) : ℕ) : ℝ) + (b : ℝ) := by linarith
  have hlower : c s + j - (c s + i)
      ≤ wordDist D.alphabet.carrier (vertex v w (c s + i))
          (vertex v w (c s + j)) + b := by exact_mod_cast hlow'
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

/-! ## Four-gons with named corners -/

/-- **A 4-gon with its cut function named, and its first side exempt.**  The
content is that of `IsQuasiGeodesicPolygon D 1 0 4 v w` with the cut function
carried rather than existentially bound --- Lemma 4.16's construction names the
corners `vertex v w (c t)` in four different cases and compares them with each
other, so it cannot re-open an existential consistently --- **and with side `0`
exempt from the geodesic clause**.

The exemption is Dahmani--Guirardel--Osin's, not a weakening for convenience.
Their Definition 4.13 asks the sides of a polygon to be quasi-geodesic *except*
for those that are components of it, and side `0` is where the distinguished
`H lam`-component sits.  Demanding the clause of it as well is what forced the
recut of a straddling component to pay `b ↦ b + 1`, and it is not available in
the first place: a component is a run of `lam`-letters whose endpoints are one
alphabet letter apart, so a run of length `n > 1` is never a geodesic chain.

What the exemption costs is the thinness instance for side `0`: the quadrangle
lemma feeds all four sides in, and only three of them are chains now.
`exists_isBetween_of_quadrangle` is the form that survives --- it produces a
between-point on the exempt side instead of an index, which is all the
corner-offset count needs, since that alternative is discarded rather than
used. -/
structure GeodesicFourGon (D : RelGenSet G Λ) (b : ℕ) (v : G)
    (w : List (RelLetter G Λ)) (c : ℕ → ℕ) : Prop where
  /-- Every letter is admissible. -/
  letters : ∀ a ∈ w, D.IsLetter a
  /-- The path closes up. -/
  closed : RelLetter.listVal w = 1
  /-- The first corner is the basepoint. -/
  start : c 0 = 0
  /-- The last corner closes the word. -/
  finish : c 4 = w.length
  /-- The corners are in order. -/
  mono : Monotone c
  /-- Each side other than the distinguished one is `(1,b)`-quasi-geodesic. -/
  geodesic : ∀ t : ℕ, t < 4 → t ≠ 0 →
    IsQuasiGeodesicChain D.alphabet.carrier b
      (fun m => vertex v w (c t + m)) (c (t + 1) - c t)

/-- **Every `(1,0)`-quasi-geodesic 4-gon is one, with its cut function named.**
The exempt form is weaker, so a polygon all of whose sides are geodesic is one
of these; the converse is what the exemption buys and is not claimed. -/
theorem exists_geodesicFourGon_of_isQuasiGeodesicPolygon (D : RelGenSet G Λ)
    {b : ℕ} {v : G} {w : List (RelLetter G Λ)}
    (hP : IsQuasiGeodesicPolygon D 1 (b : ℝ) 4 v w) :
    ∃ c : ℕ → ℕ, GeodesicFourGon D b v w c := by
  obtain ⟨c, hc0, hc4, hmono, hchain⟩ :=
    exists_geodesicChain_of_isQuasiGeodesicPolygon D hP
  exact ⟨c, hP.1, hP.2.1, hc0, hc4, hmono, fun t ht _ => hchain t ht⟩

/-- **A component filling a *non-exempt* side of a geodesic 4-gon is a single
letter.**

This is Dahmani--Guirardel--Osin's normalisation of a component to one edge, and
on a geodesic side at `μ = 1`, `b = 0` it costs nothing: the span of a component
lies in `H lam`, hence is one letter of the alphabet, so the two ends of the
side are at distance at most one, while a geodesic side realises its length as
that distance.

The hypothesis `t ≠ 0` is the exemption showing through, and it is not a defect:
side `0` is exactly the side that may carry a long run, and collapsing that run
is what `DGOIsolatedComponentNormalise.normWord` does.  For general `(μ, b)` the
same collapse is needed on every side. -/
theorem GeodesicFourGon.isComp_side_succ (D : RelGenSet G Λ) {v : G}
    {w : List (RelLetter G Λ)} {c : ℕ → ℕ} (hQ : GeodesicFourGon D 0 v w c)
    {lam : Λ} {t : ℕ} (ht : t < 4) (ht0 : t ≠ 0)
    (hcomp : IsComp lam w (c t) (c (t + 1))) :
    c (t + 1) = c t + 1 := by
  have hcs : c t ≤ c (t + 1) := hQ.mono (Nat.le_succ t)
  have hEq : c t + (c (t + 1) - c t) = c (t + 1) := by omega
  have h0 : wordDist D.alphabet.carrier (vertex v w (c t + 0))
      (vertex v w (c t + (c (t + 1) - c t))) = c (t + 1) - c t - 0 :=
    (hQ.geodesic t ht ht0).isGeodesicChain 0 (c (t + 1) - c t) (Nat.zero_le _)
      le_rfl
  rw [Nat.add_zero, hEq, Nat.sub_zero] at h0
  exact isComp_eq_succ_of_geodesic D lam v hQ.letters hcomp (le_of_eq h0.symm)

end OsinComponents
end GGT
end GroupApproximation
