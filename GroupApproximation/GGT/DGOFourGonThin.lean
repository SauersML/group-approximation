import GroupApproximation.GGT.DGOCycleAssembly

/-!
# Thinness of a geodesic four-gon, at absolute indices

`exists_index_wordDist_le_of_quadrangle` is stated for four abstract geodesic
chains closing up.  Lemma 4.16 needs it for the sides of a `GeodesicFourGon`,
with the answer as an index into `w` rather than into a side, because the cycle
it builds is cut out of `w` at absolute positions.  This module supplies the two
instances the construction uses.

## Why two, and only two

The construction offsets along the side *following* the distinguished component
(`exists_index_close_side_one`) or along the side *preceding* it
(`exists_index_close_side_three`).  Each needs the quadrangle read in cyclic
order starting at its own side --- `(1,2,3,0)` and `(3,0,1,2)` --- and those two
orders are written out here rather than being obtained from a rotation lemma.
Dahmani--Guirardel--Osin get both from "changing the enumeration of the sides";
two explicit instances are cheaper than formalising that.

Three of the four corner identities in each instance are index arithmetic on the
cut function.  The fourth is the closure of the path, `vertex v w (c 4) = v`,
which is `GeodesicFourGon.vertex_last`: it is the only place the four sides are
known to form a *closed* quadrangle rather than a chain of four.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- Rewriting a vertex along an index identity. -/
theorem vertex_congr (v : G) (w : List (RelLetter G Λ)) {x y : ℕ} (h : x = y) :
    vertex v w x = vertex v w y := by rw [h]

/-- **Thinness at the side following the component.**  A vertex of side `1` is
within `10 δ` of a vertex of side `2`, side `3` or side `0`.

The four sides are named with their lengths written as `c 2 - c 1` rather than
`c (1 + 1) - c 1`.  That is not cosmetic: the field `GeodesicFourGon.geodesic`
produces the successor form, and `omega` treats `c (1 + 1)` and `c 2` as
unrelated atoms, so the range bounds in the conclusion would not follow from the
chain bounds.  Ascribing each chain its normalised type forces the defeq once,
here, instead of leaving it to every arithmetic step downstream. -/
theorem GeodesicFourGon.exists_index_close_side_one (D : RelGenSet G Λ) {v : G}
    {w : List (RelLetter G Λ)} {c : ℕ → ℕ} (hQ : GeodesicFourGon D v w c)
    {δ : ℕ} (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ)
    {i : ℕ} (hi1 : c 1 ≤ i) (hi2 : i ≤ c 2) :
    ∃ p : ℕ, wordDist D.alphabet.carrier (vertex v w i) (vertex v w p) ≤ 10 * δ
      ∧ ((c 2 ≤ p ∧ p ≤ c 3) ∨ (c 3 ≤ p ∧ p ≤ c 4) ∨ p ≤ c 1) := by
  have hS := D.alphabet.symmetricGenerating
  have hm0 : c 0 ≤ c 1 := hQ.mono (by omega : (0 : ℕ) ≤ 1)
  have hm1 : c 1 ≤ c 2 := hQ.mono (by omega : (1 : ℕ) ≤ 2)
  have hm2 : c 2 ≤ c 3 := hQ.mono (by omega : (2 : ℕ) ≤ 3)
  have hm3 : c 3 ≤ c 4 := hQ.mono (by omega : (3 : ℕ) ≤ 4)
  have hg0 : IsGeodesicChain D.alphabet.carrier (fun m => vertex v w (c 0 + m))
      (c 1 - c 0) := hQ.geodesic 0 (by omega)
  have hg1 : IsGeodesicChain D.alphabet.carrier (fun m => vertex v w (c 1 + m))
      (c 2 - c 1) := hQ.geodesic 1 (by omega)
  have hg2 : IsGeodesicChain D.alphabet.carrier (fun m => vertex v w (c 2 + m))
      (c 3 - c 2) := hQ.geodesic 2 (by omega)
  have hg3 : IsGeodesicChain D.alphabet.carrier (fun m => vertex v w (c 3 + m))
      (c 4 - c 3) := hQ.geodesic 3 (by omega)
  have hclose : vertex v w (c 0 + 0) = vertex v w (c 3 + (c 4 - c 3)) := by
    rw [vertex_congr v w (by omega : c 3 + (c 4 - c 3) = c 4), hQ.vertex_last D,
      vertex_congr v w (by omega : c 0 + 0 = c 0), hQ.start, vertex_zero]
  have hres := exists_index_wordDist_le_of_quadrangle hS hδ hg1 hg2 hg3 hg0
    (vertex_congr v w (by omega : c 2 + 0 = c 1 + (c 2 - c 1)))
    (vertex_congr v w (by omega : c 3 + 0 = c 2 + (c 3 - c 2)))
    hclose
    (vertex_congr v w (by omega : c 0 + (c 1 - c 0) = c 1 + 0))
    (by omega : i - c 1 ≤ c 2 - c 1)
  have hiv : vertex v w (c 1 + (i - c 1)) = vertex v w i :=
    vertex_congr v w (by omega)
  rcases hres with ⟨j, hj, hd⟩ | ⟨j, hj, hd⟩ | ⟨j, hj, hd⟩
  · exact ⟨c 2 + j, by rw [← hiv]; exact hd, Or.inl ⟨by omega, by omega⟩⟩
  · exact ⟨c 3 + j, by rw [← hiv]; exact hd, Or.inr (Or.inl ⟨by omega, by omega⟩)⟩
  · exact ⟨c 0 + j, by rw [← hiv]; exact hd, Or.inr (Or.inr (by omega))⟩

/-- **Thinness at the side preceding the component.**  A vertex of side `3` is
within `10 δ` of a vertex of side `0`, side `1` or side `2`.  The chains are
ascribed their normalised lengths for the reason given above. -/
theorem GeodesicFourGon.exists_index_close_side_three (D : RelGenSet G Λ) {v : G}
    {w : List (RelLetter G Λ)} {c : ℕ → ℕ} (hQ : GeodesicFourGon D v w c)
    {δ : ℕ} (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ)
    {i : ℕ} (hi1 : c 3 ≤ i) (hi2 : i ≤ c 4) :
    ∃ p : ℕ, wordDist D.alphabet.carrier (vertex v w i) (vertex v w p) ≤ 10 * δ
      ∧ (p ≤ c 1 ∨ (c 1 ≤ p ∧ p ≤ c 2) ∨ (c 2 ≤ p ∧ p ≤ c 3)) := by
  have hS := D.alphabet.symmetricGenerating
  have hm0 : c 0 ≤ c 1 := hQ.mono (by omega : (0 : ℕ) ≤ 1)
  have hm1 : c 1 ≤ c 2 := hQ.mono (by omega : (1 : ℕ) ≤ 2)
  have hm2 : c 2 ≤ c 3 := hQ.mono (by omega : (2 : ℕ) ≤ 3)
  have hm3 : c 3 ≤ c 4 := hQ.mono (by omega : (3 : ℕ) ≤ 4)
  have hg0 : IsGeodesicChain D.alphabet.carrier (fun m => vertex v w (c 0 + m))
      (c 1 - c 0) := hQ.geodesic 0 (by omega)
  have hg1 : IsGeodesicChain D.alphabet.carrier (fun m => vertex v w (c 1 + m))
      (c 2 - c 1) := hQ.geodesic 1 (by omega)
  have hg2 : IsGeodesicChain D.alphabet.carrier (fun m => vertex v w (c 2 + m))
      (c 3 - c 2) := hQ.geodesic 2 (by omega)
  have hg3 : IsGeodesicChain D.alphabet.carrier (fun m => vertex v w (c 3 + m))
      (c 4 - c 3) := hQ.geodesic 3 (by omega)
  have hclose : vertex v w (c 0 + 0) = vertex v w (c 3 + (c 4 - c 3)) := by
    rw [vertex_congr v w (by omega : c 3 + (c 4 - c 3) = c 4), hQ.vertex_last D,
      vertex_congr v w (by omega : c 0 + 0 = c 0), hQ.start, vertex_zero]
  have hres := exists_index_wordDist_le_of_quadrangle hS hδ hg3 hg0 hg1 hg2
    hclose
    (vertex_congr v w (by omega : c 1 + 0 = c 0 + (c 1 - c 0)))
    (vertex_congr v w (by omega : c 2 + 0 = c 1 + (c 2 - c 1)))
    (vertex_congr v w (by omega : c 2 + (c 3 - c 2) = c 3 + 0))
    (by omega : i - c 3 ≤ c 4 - c 3)
  have hiv : vertex v w (c 3 + (i - c 3)) = vertex v w i :=
    vertex_congr v w (by omega)
  rcases hres with ⟨j, hj, hd⟩ | ⟨j, hj, hd⟩ | ⟨j, hj, hd⟩
  · exact ⟨c 0 + j, by rw [← hiv]; exact hd, Or.inl (by omega)⟩
  · exact ⟨c 1 + j, by rw [← hiv]; exact hd, Or.inr (Or.inl ⟨by omega, by omega⟩)⟩
  · exact ⟨c 2 + j, by rw [← hiv]; exact hd, Or.inr (Or.inr ⟨by omega, by omega⟩)⟩

end OsinComponents
end GGT
end GroupApproximation
