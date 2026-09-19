import GroupApproximation.GGT.DGOCycleAssembly

/-!
# Thinness of a quasi-geodesic four-gon, at absolute indices

`exists_isBetween_of_quadrangle` is stated for four abstract corners and a point
between the first two.  Lemma 4.16 needs it for the sides of a
`GeodesicFourGon`, with the answer as an index into `w` rather than into a side,
because the cycle it builds is cut out of `w` at absolute positions.  This
module supplies the two instances the construction uses, at `(1,b)`.

## Why two, and only two

The construction offsets along the side *following* the distinguished component
(`exists_index_close_side_one`) or along the side *preceding* it
(`exists_index_close_side_three`).  Each needs the quadrangle read in cyclic
order starting at its own side --- `(1,2,3,0)` and `(3,0,1,2)` --- and those two
orders are written out here rather than being obtained from a rotation lemma.
Dahmani--Guirardel--Osin get both from "changing the enumeration of the sides";
two explicit instances are cheaper than formalising that.

## Why the answer is a disjunction of two kinds

Side `0` is **exempt** from the quasi-geodesic clause of `GeodesicFourGon`, so
no index can be produced on it: the half-step
`exists_index_wordDist_le_of_isBetween_quasi` from a between-point to a vertex is
exactly what needs a chain.  Both instances therefore return *either* an index
on one of the two non-exempt sides they can reach, *or* a point between the
basepoint `v` and the far end `vertex v w (c 1)` of the distinguished side.

That is enough, because the second alternative is never used --- it is
*discarded*.  The two ends of the distinguished side lie in one coset of
`H lam`, so they are one alphabet letter apart, so every point between them is
within `1` of `v`; and the offset that produced the source vertex put it at
least `θ + 2` from `v`.  The near point of the thinness cannot be there.

## The constant, and where `b` enters

Three steps, in this order:

* the source vertex is only `b`-**almost** between its side's corners
  (`IsQuasiGeodesicChain.isAlmostBetween`), so it is first replaced by a genuine
  between-point at cost `b + 2δ`
  (`exists_isBetween_near_of_isAlmostBetween`);
* `exists_isBetween_of_quadrangle` moves that to a between-point of another
  side's chord, at cost `8δ` in the worst alternative;
* the half-step returns an indexed vertex at cost `2δ + b`.

So `12δ + 2b`.  At `b = 0` this is `12δ` rather than the `10δ` of the geodesic
version, because the first step costs `2δ` even when the source is already
between: a uniform statement cannot be sharp at both ends, and one case tree was
preferred to two.
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
within `12 δ + 2 b` of a vertex of side `2` or side `3`, or else within
`12 δ + 2 b` of a point between the basepoint and the far end of the exempt
side `0`.

The four sides are named with their lengths written as `c 2 - c 1` rather than
`c (1 + 1) - c 1`.  That is not cosmetic: the field `GeodesicFourGon.geodesic`
produces the successor form, and `omega` treats `c (1 + 1)` and `c 2` as
unrelated atoms, so the range bounds in the conclusion would not follow from the
chain bounds.  Ascribing each chain its normalised type forces the defeq once,
here, instead of leaving it to every arithmetic step downstream. -/
theorem GeodesicFourGon.exists_index_close_side_one (D : RelGenSet G Λ) {b : ℕ}
    {v : G} {w : List (RelLetter G Λ)} {c : ℕ → ℕ}
    (hQ : GeodesicFourGon D b v w c)
    {δ : ℕ} (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ)
    {i : ℕ} (hi1 : c 1 ≤ i) (hi2 : i ≤ c 2) :
    (∃ p : ℕ,
        wordDist D.alphabet.carrier (vertex v w i) (vertex v w p)
            ≤ 12 * δ + 2 * b ∧
          ((c 2 ≤ p ∧ p ≤ c 3) ∨ (c 3 ≤ p ∧ p ≤ c 4))) ∨
      (∃ q : G, Hyperbolic.IsBetween D.alphabet.carrier v q (vertex v w (c 1)) ∧
        wordDist D.alphabet.carrier (vertex v w i) q ≤ 12 * δ + 2 * b) := by
  have hS := D.alphabet.symmetricGenerating
  have hm1 : c 1 ≤ c 2 := hQ.mono (by omega : (1 : ℕ) ≤ 2)
  have hm2 : c 2 ≤ c 3 := hQ.mono (by omega : (2 : ℕ) ≤ 3)
  have hm3 : c 3 ≤ c 4 := hQ.mono (by omega : (3 : ℕ) ≤ 4)
  have hg1 : IsQuasiGeodesicChain D.alphabet.carrier b
      (fun m => vertex v w (c 1 + m)) (c 2 - c 1) := hQ.geodesic 1 (by omega)
        (by omega)
  have hg2 : IsQuasiGeodesicChain D.alphabet.carrier b
      (fun m => vertex v w (c 2 + m)) (c 3 - c 2) := hQ.geodesic 2 (by omega)
        (by omega)
  have hg3 : IsQuasiGeodesicChain D.alphabet.carrier b
      (fun m => vertex v w (c 3 + m)) (c 4 - c 3) := hQ.geodesic 3 (by omega)
        (by omega)
  have hlast : vertex v w (c 4) = v := hQ.vertex_last D
  -- the source vertex is only `b`-almost between the corners of its side
  have halm : IsAlmostBetween D.alphabet.carrier b (vertex v w (c 1))
      (vertex v w i) (vertex v w (c 2)) := by
    have h := hg1.isAlmostBetween (show i - c 1 ≤ c 2 - c 1 by omega)
    rwa [show c 1 + 0 = c 1 from by omega,
      show c 1 + (i - c 1) = i from by omega,
      show c 1 + (c 2 - c 1) = c 2 from by omega] at h
  obtain ⟨p', hp', hpd⟩ := exists_isBetween_near_of_isAlmostBetween hS hδ halm
  rcases exists_isBetween_of_quadrangle hS hδ hp' (x₃ := vertex v w (c 3))
      (x₄ := v) with ⟨q, hq, hd⟩ | ⟨q, hq, hd⟩ | ⟨q, hq, hd⟩
  · -- the near point is on side `2`
    have hq' : Hyperbolic.IsBetween D.alphabet.carrier (vertex v w (c 2 + 0)) q
        (vertex v w (c 2 + (c 3 - c 2))) := by
      rw [show c 2 + 0 = c 2 from by omega,
        show c 2 + (c 3 - c 2) = c 3 from by omega]
      exact hq
    obtain ⟨j, hjn, hj⟩ :=
      exists_index_wordDist_le_of_isBetween_quasi hS hδ hg2 hq'
    refine Or.inl ⟨c 2 + j, ?_, Or.inl ⟨by omega, by omega⟩⟩
    have htri1 := wordDist_triangle hS (vertex v w i) p' q
    have htri2 := wordDist_triangle hS (vertex v w i) q (vertex v w (c 2 + j))
    omega
  · -- the near point is on side `3`
    have hq' : Hyperbolic.IsBetween D.alphabet.carrier (vertex v w (c 3 + 0)) q
        (vertex v w (c 3 + (c 4 - c 3))) := by
      rw [show c 3 + 0 = c 3 from by omega,
        show c 3 + (c 4 - c 3) = c 4 from by omega, hlast]
      exact hq
    obtain ⟨j, hjn, hj⟩ :=
      exists_index_wordDist_le_of_isBetween_quasi hS hδ hg3 hq'
    refine Or.inl ⟨c 3 + j, ?_, Or.inr ⟨by omega, by omega⟩⟩
    have htri1 := wordDist_triangle hS (vertex v w i) p' q
    have htri2 := wordDist_triangle hS (vertex v w i) q (vertex v w (c 3 + j))
    omega
  · -- the near point is on the exempt side `0`
    refine Or.inr ⟨q, hq, ?_⟩
    have htri1 := wordDist_triangle hS (vertex v w i) p' q
    omega

/-- **Thinness at the side preceding the component.**  A vertex of side `3` is
within `12 δ + 2 b` of a vertex of side `1` or side `2`, or else within
`12 δ + 2 b` of a point between the basepoint and the far end of the exempt
side `0`.  The chains are ascribed their normalised lengths for the reason given
above. -/
theorem GeodesicFourGon.exists_index_close_side_three (D : RelGenSet G Λ)
    {b : ℕ} {v : G} {w : List (RelLetter G Λ)} {c : ℕ → ℕ}
    (hQ : GeodesicFourGon D b v w c)
    {δ : ℕ} (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ)
    {i : ℕ} (hi1 : c 3 ≤ i) (hi2 : i ≤ c 4) :
    (∃ p : ℕ,
        wordDist D.alphabet.carrier (vertex v w i) (vertex v w p)
            ≤ 12 * δ + 2 * b ∧
          ((c 1 ≤ p ∧ p ≤ c 2) ∨ (c 2 ≤ p ∧ p ≤ c 3))) ∨
      (∃ q : G, Hyperbolic.IsBetween D.alphabet.carrier v q (vertex v w (c 1)) ∧
        wordDist D.alphabet.carrier (vertex v w i) q ≤ 12 * δ + 2 * b) := by
  have hS := D.alphabet.symmetricGenerating
  have hm1 : c 1 ≤ c 2 := hQ.mono (by omega : (1 : ℕ) ≤ 2)
  have hm2 : c 2 ≤ c 3 := hQ.mono (by omega : (2 : ℕ) ≤ 3)
  have hm3 : c 3 ≤ c 4 := hQ.mono (by omega : (3 : ℕ) ≤ 4)
  have hg1 : IsQuasiGeodesicChain D.alphabet.carrier b
      (fun m => vertex v w (c 1 + m)) (c 2 - c 1) := hQ.geodesic 1 (by omega)
        (by omega)
  have hg2 : IsQuasiGeodesicChain D.alphabet.carrier b
      (fun m => vertex v w (c 2 + m)) (c 3 - c 2) := hQ.geodesic 2 (by omega)
        (by omega)
  have hg3 : IsQuasiGeodesicChain D.alphabet.carrier b
      (fun m => vertex v w (c 3 + m)) (c 4 - c 3) := hQ.geodesic 3 (by omega)
        (by omega)
  have hlast : vertex v w (c 4) = v := hQ.vertex_last D
  have halm : IsAlmostBetween D.alphabet.carrier b (vertex v w (c 3))
      (vertex v w i) v := by
    have h := hg3.isAlmostBetween (show i - c 3 ≤ c 4 - c 3 by omega)
    rwa [show c 3 + 0 = c 3 from by omega,
      show c 3 + (i - c 3) = i from by omega,
      show c 3 + (c 4 - c 3) = c 4 from by omega, hlast] at h
  obtain ⟨p', hp', hpd⟩ := exists_isBetween_near_of_isAlmostBetween hS hδ halm
  rcases exists_isBetween_of_quadrangle hS hδ hp' (x₃ := vertex v w (c 1))
      (x₄ := vertex v w (c 2)) with ⟨q, hq, hd⟩ | ⟨q, hq, hd⟩ | ⟨q, hq, hd⟩
  · -- the near point is on the exempt side `0`
    refine Or.inr ⟨q, hq, ?_⟩
    have htri1 := wordDist_triangle hS (vertex v w i) p' q
    omega
  · -- the near point is on side `1`
    have hq' : Hyperbolic.IsBetween D.alphabet.carrier (vertex v w (c 1 + 0)) q
        (vertex v w (c 1 + (c 2 - c 1))) := by
      rw [show c 1 + 0 = c 1 from by omega,
        show c 1 + (c 2 - c 1) = c 2 from by omega]
      exact hq
    obtain ⟨j, hjn, hj⟩ :=
      exists_index_wordDist_le_of_isBetween_quasi hS hδ hg1 hq'
    refine Or.inl ⟨c 1 + j, ?_, Or.inl ⟨by omega, by omega⟩⟩
    have htri1 := wordDist_triangle hS (vertex v w i) p' q
    have htri2 := wordDist_triangle hS (vertex v w i) q (vertex v w (c 1 + j))
    omega
  · -- the near point is on side `2`
    have hq' : Hyperbolic.IsBetween D.alphabet.carrier (vertex v w (c 2 + 0)) q
        (vertex v w (c 2 + (c 3 - c 2))) := by
      rw [show c 2 + 0 = c 2 from by omega,
        show c 2 + (c 3 - c 2) = c 3 from by omega]
      exact hq
    obtain ⟨j, hjn, hj⟩ :=
      exists_index_wordDist_le_of_isBetween_quasi hS hδ hg2 hq'
    refine Or.inl ⟨c 2 + j, ?_, Or.inr ⟨by omega, by omega⟩⟩
    have htri1 := wordDist_triangle hS (vertex v w i) p' q
    have htri2 := wordDist_triangle hS (vertex v w i) q (vertex v w (c 2 + j))
    omega

end OsinComponents
end GGT
end GroupApproximation
