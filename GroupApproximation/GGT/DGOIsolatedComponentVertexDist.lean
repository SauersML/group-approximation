import GroupApproximation.GGT.OsinTheorem54SepFourGonGeneral
import GroupApproximation.GGT.OsinTheorem54SepComponents

/-!
# Vertices of connected components are one letter apart

Dahmani--Guirardel--Osin's Lemma 4.16 excludes a coset hit by a distance count:
*if a component `s` of the connector were connected to the distinguished
component `p₁`, then `d(x₂, s₋) ≤ 1`*, and that contradicts the chosen offset.
This module supplies the step in italics, in the form the count needs --- for
*any* two vertices of the two components, not only their initial ones.

Concept grep before writing: `wordDist_le_one` and `connected` across the tree.
What exists is `wordDist_le_one_of_mem_fam` (SepFourGonGeneral), the group-level
statement that an element of `H lam` is one letter, and its two consumers
`index_le_of_connector` (SepFourGonPinning) and `notMem_coset_of_offset`
(DGOPolygonGeodesicChain), which apply it at *corners*.  The vertex-to-vertex
form is not in the tree; `Connected` itself is only about component starts.

## What is proved

* `span_mem_fam_of_mem_comp` --- every vertex of a component lies in the coset of
  its initial vertex.  This is `span_mem_fam` (SepComponents) restricted to the
  run, and it is the only thing the two distance statements use.
* `wordDist_vertex_le_one_of_mem_comp` --- any two vertices of one component are
  at most one letter apart.  At `(μ,b) = (1,0)` this is what forces a component
  inside a geodesic side to be a single letter
  (`GeodesicFourGon.isComp_side_succ`); the general statement does not need the
  component to be a side, or the polygon to exist at all.
* `wordDist_vertex_le_one_of_connected` --- any vertex of one component and any
  vertex of a component connected to it are at most one letter apart.

At the two component *starts* no wrapper is needed at all: `Connected` unfolds to
`wordDist_le_one_of_mem_fam`'s hypothesis, so `wordDist_le_one_of_mem_fam D hconn`
typechecks directly, and a restatement of that was removed from this module rather
than carried.  What is here is the case where the vertices are not the starts.

None of the three needs a polygon, hyperbolicity, or isolation: connectedness is
membership in one coset of `H lam`, and a coset difference is a single letter of
`X ⊔ ℋ`.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## Every vertex of a component lies in the coset of its start -/

/-- **A vertex of a component is in the coset of the component's start.**  The
letters between are `lam`-letters, so `span_mem_fam` applies to the truncated
run. -/
theorem span_mem_fam_of_mem_comp (D : RelGenSet G Λ) (lam : Λ) (v : G)
    {w : List (RelLetter G Λ)} (hlet : ∀ a ∈ w, D.IsLetter a) {i k p : ℕ}
    (hcomp : IsComp lam w i k) (hip : i ≤ p) (hpk : p ≤ k) :
    (vertex v w i)⁻¹ * vertex v w p ∈ D.fam lam := by
  obtain ⟨-, hkw, hrange, -, -⟩ := hcomp
  exact span_mem_fam D lam v hlet p (by omega) i hip
    (fun j hj1 hj2 hj3 => hrange j hj1 (by omega) hj3)

/-! ## Two vertices of one component -/

/-- **Any two vertices of one `H lam`-component are one letter apart.**  Both
lie in the coset of the component's start, so their difference lies in `H lam`,
and an element of `H lam` is a letter of `X ⊔ ℋ`. -/
theorem wordDist_vertex_le_one_of_mem_comp (D : RelGenSet G Λ) (lam : Λ) (v : G)
    {w : List (RelLetter G Λ)} (hlet : ∀ a ∈ w, D.IsLetter a) {i k p q : ℕ}
    (hcomp : IsComp lam w i k) (hip : i ≤ p) (hpk : p ≤ k) (hiq : i ≤ q)
    (hqk : q ≤ k) :
    wordDist D.alphabet.carrier (vertex v w p) (vertex v w q) ≤ 1 := by
  have h1 := span_mem_fam_of_mem_comp D lam v hlet hcomp hip hpk
  have h2 := span_mem_fam_of_mem_comp D lam v hlet hcomp hiq hqk
  refine wordDist_le_one_of_mem_fam D (lam := lam) ?_
  have hrw : (vertex v w p)⁻¹ * vertex v w q
      = ((vertex v w i)⁻¹ * vertex v w p)⁻¹ * ((vertex v w i)⁻¹ * vertex v w q) := by
    group
  rw [hrw]
  exact mul_mem (inv_mem h1) h2

/-! ## Two vertices of two connected components -/

/-- **Any vertex of one component and any vertex of a component connected to it
are one letter apart.**

This is the step Dahmani--Guirardel--Osin's Lemma 4.16 uses to exclude a coset
hit: a component of the connector connected to the distinguished component would
put one of its vertices within one letter of a corner, which the offset forbids.
The two components are not required to be distinct, nor isolated, nor to lie on
sides of any polygon. -/
theorem wordDist_vertex_le_one_of_connected (D : RelGenSet G Λ) (lam : Λ) (v : G)
    {w : List (RelLetter G Λ)} (hlet : ∀ a ∈ w, D.IsLetter a)
    {i k i' k' p q : ℕ} (hcomp : IsComp lam w i k) (hcomp' : IsComp lam w i' k')
    (hconn : Connected D.fam lam v w i i') (hip : i ≤ p) (hpk : p ≤ k)
    (hiq : i' ≤ q) (hqk : q ≤ k') :
    wordDist D.alphabet.carrier (vertex v w p) (vertex v w q) ≤ 1 := by
  have h1 := span_mem_fam_of_mem_comp D lam v hlet hcomp hip hpk
  have h2 := span_mem_fam_of_mem_comp D lam v hlet hcomp' hiq hqk
  have hconn' : (vertex v w i)⁻¹ * vertex v w i' ∈ D.fam lam := hconn
  refine wordDist_le_one_of_mem_fam D (lam := lam) ?_
  have hrw : (vertex v w p)⁻¹ * vertex v w q
      = ((vertex v w i)⁻¹ * vertex v w p)⁻¹ *
        (((vertex v w i)⁻¹ * vertex v w i') * ((vertex v w i')⁻¹ * vertex v w q)) := by
    group
  rw [hrw]
  exact mul_mem (inv_mem h1) (mul_mem hconn' h2)


end OsinComponents
end GGT
end GroupApproximation
