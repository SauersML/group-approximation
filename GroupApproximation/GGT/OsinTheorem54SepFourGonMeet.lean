import GroupApproximation.GGT.OsinTheorem54SepPolygonVertex

/-!
# Trivial connectors: what they force, and what they do not

A consumer asked whether a long match with **trivial connectors** between a word
and a rotation of itself forces the rotation offset to be zero.  The two facts
below settle the polygon half of that, and they point in opposite directions.

## What trivial connectors do force

* `vertex_eq_of_trivial_connector` --- with the connector trivial *and* the
  short side trivial, the two long sides literally **meet** at the matched
  vertices: `vertex 1 q i = vertex 1 s j`.  So "do the sides meet" is yes.
* `segment_eq_of_trivial_connectors` --- with two matched blocks and trivial
  connectors, the segment of `q` between them spells **the same element** as the
  segment of `s` between them, whatever the short side is.  The short side
  cancels, exactly as in `wordDist_connector_pair`.

## What they do not force

They do not force the offset to be zero, and no polygon hypothesis can.  Take
`w` a power of one letter, `w = [base a]` repeated `N` times.  Then
`w.rotate δ = w` **as a list**, for every `δ` --- Mathlib's
`List.rotate_replicate` --- so the point needs no lemma of its own.  The
quadrilateral built from `(w, w.rotate δ)` is then literally the one built from
`(w, w)`: the same
four words, the same matches, the same connectors, the same everything.  No
predicate on that data can be `δ = 0` for one and refute it for another, since
the data does not mention `δ`.

The property that rules the offset out is therefore a property of the *word* --
that it admits no nontrivial period of the relevant size -- and not of the
polygon.  `segment_eq_of_trivial_connectors` is the exact reduction: it turns a
match with trivial connectors into a coincidence between two segments of one
word, and aperiodicity is what forbids that coincidence.  A block design with
distinct exponents supplies it directly; the four-gon machinery never will.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **With a trivial connector and a trivial short side, the two long sides meet
at the matched vertices.** -/
theorem vertex_eq_of_trivial_connector (q s : List (RelLetter G Λ)) {i j : ℕ}
    (he : (1 : G) * vertex (1 : G) q i * 1 = vertex (1 : G) s j) :
    vertex (1 : G) q i = vertex (1 : G) s j := by
  rw [← he]
  group

/-- **Trivial connectors at two matched blocks make the two segments spell the
same element.**

The short side cancels: this is the same mechanism as `wordDist_connector_pair`,
with the two connectors taken to be `1` rather than merely short, so the
conclusion is an equality rather than an estimate.

This is the exact reduction of "a long match with trivial connectors" to a
coincidence between two segments of the ambient words.  When `s` is a rotation
of `q`, both segments live in one word, and forbidding the coincidence is a
periodicity statement about that word --- not something the quadrilateral
knows. -/
theorem segment_eq_of_trivial_connectors (p q s : List (RelLetter G Λ))
    {i₁ i₂ j₁ j₂ : ℕ}
    (he₁ : RelLetter.listVal p * vertex (1 : G) q i₁ * 1 = vertex (1 : G) s j₁)
    (he₂ : RelLetter.listVal p * vertex (1 : G) q i₂ * 1 = vertex (1 : G) s j₂) :
    (vertex (1 : G) q i₁)⁻¹ * vertex (1 : G) q i₂
      = (vertex (1 : G) s j₁)⁻¹ * vertex (1 : G) s j₂ := by
  rw [← he₁, ← he₂]
  group


end OsinComponents
end GGT
end GroupApproximation
