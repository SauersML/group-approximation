import GroupApproximation.GGT.KazhdanHypGirthEightVKInterface
import GroupApproximation.GGT.OsinGeodesicWord

/-!
# Geodesic words at Cayley vertices

The metric vertex `Cayley.of A g` stores the group element `g`.  A geodesic
edge path between two such vertices is read by its relative letters.  The
relative-word API packages exactly the three facts needed by the
girth-eight construction: every dart label is allowed, the ordered product
is the endpoint difference, and the number of darts is the Cayley distance.

`OsinComponents.existsGeodesicWord` is the landed finite-word producer.  This
file gives it the named endpoint-facing theorem
`exists_geodesicWord_of_dist`, and keeps the Cayley endpoint specialization
next to it.  No geometric realization of arbitrary metric points is used;
the presentation consumers only use Cayley vertices.
-/

namespace GroupApproximation
namespace GGT
namespace KazhdanHypGirthEightGeodesicWord

open GroupApproximation.WordMetric
open GroupApproximation.GGT.OsinComponents
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

variable {G : Type u} [Group G] {Lambda : Type w}

/-! ## The endpoint certificate -/

/-- A relative word read from `f` and ending at `g`, with the least possible
number of letters.  The final equality is the natural-number distance used by
the presentation's Cayley graph. -/
structure GeodesicWordCertificate
    (D : RelGenSet G Lambda) (f g : G) where
  word : List (RelLetter G Lambda)
  geodesic : IsGeodesicWord D f g word
  endpoint : f * RelLetter.listVal word = g
  length_eq_dist : word.length = wordDist D.alphabet.carrier f g

/-- The landed relative-word producer supplies the certificate at every pair
of Cayley vertices. -/
theorem exists_geodesicWord_of_dist
    (D : RelGenSet G Lambda) (f g : G) :
    ∃ W : GeodesicWordCertificate D f g, W.word.length =
      wordDist D.alphabet.carrier f g := by
  obtain ⟨word, hword⟩ := existsGeodesicWord D f g
  refine ⟨{
    word := word
    geodesic := hword
    endpoint := hword.2.1
    length_eq_dist := hword.2.2 }, ?_⟩
  exact hword.2.2

/-- The certificate exposes the label/product/length conjunction in the
`IsGeodesicWord` form used by the Osin component lemmas. -/
theorem geodesicWordCertificate_spec
    {D : RelGenSet G Lambda} {f g : G}
    (W : GeodesicWordCertificate D f g) :
    (∀ a ∈ W.word, D.IsLetter a) ∧
      f * RelLetter.listVal W.word = g ∧
      W.word.length = wordDist D.alphabet.carrier f g := by
  exact W.geodesic

/-- The same finite word certificate at the named vertices of
`Cayley D.alphabet`.  The `Cayley.val` projection is the endpoint-label map
of the graph. -/
theorem exists_geodesicWord_of_cayley_dist
    (D : RelGenSet G Lambda) (x y : Cayley D.alphabet) :
    ∃ W : GeodesicWordCertificate D (Cayley.val x) (Cayley.val y),
      W.word.length = wordDist D.alphabet.carrier
        (Cayley.val x) (Cayley.val y) := by
  exact exists_geodesicWord_of_dist D (Cayley.val x) (Cayley.val y)

/-! ## A path-reading adapter -/

/-- The label list of a relative dart path is a geodesic word whenever its
endpoint and length fields have the corresponding values.  The first
conjunct is kept explicit so callers can use it without unfolding
`IsGeodesicWord`. -/
theorem geodesicWord_of_labelledPath
    {D : RelGenSet G Lambda} {f g : G}
    (word : List (RelLetter G Lambda))
    (hletters : ∀ a ∈ word, D.IsLetter a)
    (hend : f * RelLetter.listVal word = g)
    (hlen : word.length = wordDist D.alphabet.carrier f g) :
    IsGeodesicWord D f g word :=
  ⟨hletters, hend, hlen⟩

/-- Reading a shortest Cayley path gives the endpoint equation and its exact
word length.  This theorem is phrased with `Cayley.val`, so a caller can pass
the resulting word directly to the relative polygon API. -/
theorem cayleyPathWord_spec
    (D : RelGenSet G Lambda) (x y : Cayley D.alphabet) :
    ∃ word : List (RelLetter G Lambda),
      IsGeodesicWord D (Cayley.val x) (Cayley.val y) word ∧
      Cayley.val x * RelLetter.listVal word = Cayley.val y ∧
      word.length = wordDist D.alphabet.carrier
        (Cayley.val x) (Cayley.val y) := by
  obtain ⟨W, hW⟩ := exists_geodesicWord_of_cayley_dist D x y
  exact ⟨W.word, W.geodesic, W.endpoint, hW⟩

/-! ## Finite model -/

/-- At equal Cayley vertices the producer returns a zero-length relative path. -/
theorem cayleyPathWord_equal_model
    (D : RelGenSet G Lambda) (x : Cayley D.alphabet) :
    ∃ word : List (RelLetter G Lambda),
      IsGeodesicWord D (Cayley.val x) (Cayley.val x) word ∧ word.length = 0 := by
  obtain ⟨word, hword⟩ := existsGeodesicWord D (Cayley.val x) (Cayley.val x)
  refine ⟨word, hword, ?_⟩
  rw [wordDist_self] at hword
  exact hword.2.2

end KazhdanHypGirthEightGeodesicWord
end GGT
end GroupApproximation
