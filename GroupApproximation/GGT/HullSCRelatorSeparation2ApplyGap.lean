import GroupApproximation.GGT.OsinTheorem54SepFourGonPinning

/-!
# The gap between two matches, in the currency the mixed case pays in

`HullSC.false_of_span_mixed` asks for the two matches to be within `gapSlack` of
the two blocks they match: `j₂ - j₁ ≤ i₂ - i₁ + gapSlack`.  Both halves of that
are already in `GGT/OsinTheorem54SepFourGonPinning.lean`, and neither needs the
long sides to be geodesic:

* `wordDist_connector_pair` --- the short side cancels between two matches, so
  the matched pair is at most two further apart than the original pair, one for
  each connector, with no `eps` involved;
* `wordDist_vertex_le` --- the upper half a quasi-geodesic hypothesis does not
  give: the vertices at `i₁` and `i₂` are at most `i₂ - i₁` apart, whatever the
  word, because the segment between them spells the difference.

`wordDist_match_le` is the two composed, and it is the whole estimate on the
`q` side.

What remains is the lower half on the `s` side, and that is the quasi-geodesic
clause, which is stated over the reals.  `le_of_qg_one` converts it at `mu = 1`
--- the constant `HullSC.quasiGeodesic_relatorWord₂_of_blockCount` produces, so
the conversion costs the chain nothing --- and the additive shape
`false_of_span_mixed` wants comes out with `gapSlack = b + 2`.  At `mu > 1` the
estimate is multiplicative and the additive shape is not available, which is why
the block-count route is the one that has to be taken.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

section Gap

variable {G : Type u} [Group G] {Λ : Type w}

/-- **Two matches are at most `i₂ - i₁ + 2` apart.**

The connectors contribute one each and the prefix cancels; the distance along
the matched side is bounded by the number of letters between the two indices,
which needs no hypothesis on the word beyond admissibility. -/
theorem wordDist_match_le (D : RelGenSet G Λ) {lam : Λ}
    {q s : List (RelLetter G Λ)} (hlet : ∀ a ∈ q, D.IsLetter a)
    {lp h₁ h₂ : G} (hh₁ : h₁ ∈ D.fam lam) (hh₂ : h₂ ∈ D.fam lam)
    {i₁ i₂ j₁ j₂ : ℕ} (hi : i₁ ≤ i₂) (hi₂ : i₂ ≤ q.length)
    (he₁ : lp * vertex (1 : G) q i₁ * h₁ = vertex (1 : G) s j₁)
    (he₂ : lp * vertex (1 : G) q i₂ * h₂ = vertex (1 : G) s j₂) :
    wordDist D.alphabet.carrier (vertex (1 : G) s j₁) (vertex (1 : G) s j₂)
      ≤ i₂ - i₁ + 2 := by
  have h1 := wordDist_connector_pair D hh₁ hh₂ he₁ he₂
  have h2 := wordDist_vertex_le D hlet hi hi₂
  omega

/-- **The quasi-geodesic clause at `mu = 1`, in naturals.**

The clause is `(n : ℝ) / mu - b ≤ d`; at `mu = 1` it is `n ≤ d + b`, and any
natural bound on `b` turns that into the additive inequality the mixed case
consumes. -/
theorem le_of_qg_one {bb : ℝ} {n d B : ℕ} (hqg : (n : ℝ) / 1 - bb ≤ (d : ℝ))
    (hB : bb ≤ (B : ℝ)) : n ≤ d + B := by
  rw [div_one] at hqg
  have h : (n : ℝ) ≤ ((d + B : ℕ) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast h

/-- **Two connected components of one side are index-close.**

A connector lies in `H_λ`, so it is one letter of the alphabet, so the two
vertices are at distance at most one; a quasi-geodesic side then puts the two
indices within `1 + b` of each other.

This is the quasi-geodesic replacement for the adjacency step inside
`not_connected_qBlock_of_isComp`, which reads `distance ≤ 1` off as
`|i - i'| ≤ 1` and so needs the side to be GEODESIC.  The sides of the
relator quadrilateral are not: `HullSC.quasiGeodesic_relatorWord₂_of_blockCount`
makes them `(1, b)`-quasi-geodesic and no better, and at `b > 0` two connected
components of one side can be several indices apart.  What survives is that they
are BOUNDEDLY apart, and the bound depends only on the quasi-geodesic constant
-- not on the exponent list.  That is what lets the design's window clause be
set against it: `W` is chosen before `ms`, and `1 + B` is available then. -/
theorem index_close_of_connected (D : RelGenSet G Λ) {lam : Λ}
    {q : List (RelLetter G Λ)} {bb : ℝ}
    (hqg : ∀ x y : ℕ, x ≤ y → y ≤ q.length →
      ((y - x : ℕ) : ℝ) / 1 - bb
        ≤ ((wordDist D.alphabet.carrier (vertex (1 : G) q x)
              (vertex (1 : G) q y) : ℕ) : ℝ))
    {B : ℕ} (hB : bb ≤ (B : ℝ)) {i i' : ℕ} (hii : i ≤ i')
    (hi' : i' ≤ q.length)
    (hmem : (vertex (1 : G) q i)⁻¹ * vertex (1 : G) q i' ∈ D.fam lam) :
    i' - i ≤ 1 + B := by
  have hd : wordDist D.alphabet.carrier (vertex (1 : G) q i)
      (vertex (1 : G) q i') ≤ 1 := wordDist_le_one_of_mem_fam D hmem
  have h := le_of_qg_one (hqg i i' hii hi') hB
  omega

end Gap

end OsinComponents
end GGT
end GroupApproximation
