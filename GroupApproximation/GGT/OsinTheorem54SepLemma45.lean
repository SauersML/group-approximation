import GroupApproximation.GGT.OsinTheorem54SepTriangle
import GroupApproximation.GGT.OsinTheorem54SepFourGonBridge
import GroupApproximation.GGT.OsinTheorem54SepCorner45
import GroupApproximation.GGT.OsinTheorem54SepFourGonPinning

/-!
# Osin's Lemma 4.5: two geodesic segments penetrate every separating coset

A coset separating `f` from `g` is penetrated by the two-segment path
`f → h → g`, whichever geodesics the two segments are.  This is what lets
Lemma 4.9 compare `S(f,g)` against `S(f,h)` and `S(g,h)` at all.

The polygon is the triangle on the three geodesics, carried as the quadrilateral
with an empty first side, so the isolated-component bound arrives at `n = 4` and
the hypothesis is `4C ≤ Dc` where Osin writes `D ≥ 3C` (Remark 4.4).  `D` is
chosen downstream with `C` in hand, so the larger lower bound costs nothing.

## The shape of the argument

The witness is a geodesic `w : f → g` with a component essentially penetrating
the coset.  Everything then turns on ONE clause: whether that component is still
maximal in the polygon, i.e. whether the letter at its end is peripheral.

* If it is not, the component transfers, and it cannot be isolated --- the bound
  would put its span inside `relBall lam (C*4) ⊆ relBall lam Dc`, contradicting
  essentiality.  So it is connected to another component start, and there are
  three places that start can be, one per block.
* If it is, the run continues past the corner into the next block, and the
  conclusion arrives instead of the argument: that block's side has a peripheral
  letter next to `g`, so it penetrates the coset outright.

## Why the third case is not symmetric with the second

The first block's match is refuted rather than used: two distinct components of
one GEODESIC cannot be connected, which is `not_connected_qBlock_of_isComp`.
The second and third blocks are read backwards --- they are traversed against
their own orientation --- so a match there is converted through
`isCompOf_getElem_revWord'` BEFORE the component of the side is extracted, never
after: the letter across a reversal belongs to a different side, and its index
alone says nothing about which coset of `H_λ` it reads.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## The triangle's blocks, specialised from the quadrilateral -/

/-- **A component of the first side is a component of the triangle**, given
maximality at its end in the triangle. -/
theorem isComp_triangle_of_isComp_witness (ws r s : List (RelLetter G Λ))
    (lam : Λ) {i k : ℕ} (hcomp : IsComp lam ws i k)
    (hpost : ∀ hkl : k < (ws ++ r ++ revWord s).length,
      ¬ ((ws ++ r ++ revWord s)[k]'hkl).IsCompOf lam) :
    IsComp lam (ws ++ r ++ revWord s) i k := by
  have h := isComp_fourGon_of_isComp_side_of_post [] ws r s lam (by simp) hcomp
    (by simpa using hpost)
  simpa using h

/-- **A vertex in the first block is a vertex of the first side.** -/
theorem vertex_triangle_witness (ws r s : List (RelLetter G Λ)) (v : G) {t : ℕ}
    (ht : t ≤ ws.length) :
    vertex v (ws ++ r ++ revWord s) t = vertex v ws t := by
  have h := vertex_fourGon_side [] ws r s v ht
  rw [RelLetter.listVal_nil, mul_one] at h
  simpa using h.trans (vertex_eq_mul_vertex_one ws v t).symm

/-- **A vertex in the middle block is a vertex of the second side**, read from
its own basepoint and against its own orientation. -/
theorem vertex_triangle_mid_side (ws zs ys : List (RelLetter G Λ)) {f g hh : G}
    (hwv : f * RelLetter.listVal ws = g) (hzv : hh * RelLetter.listVal zs = g)
    {a : ℕ} (ha : a ≤ zs.length) :
    vertex f (ws ++ revWord zs ++ revWord ys) (ws.length + a)
      = vertex hh zs (zs.length - a) := by
  -- `m` is implicit in `vertex_fourGon_third`; naming the fact FIXES it at `a`.
  -- Passing a `by` block instead leaves `?m ≤ (revWord zs).length` open, and
  -- `rw`'s trailing `rfl` closes that by assigning `?m := (revWord zs).length`.
  have haz : a ≤ (revWord zs).length := by
    rw [length_revWord]
    exact ha
  have h := vertex_fourGon_third [] ws (revWord zs) ys f haz
  rw [RelLetter.listVal_nil, mul_one,
    ← vertex_eq_mul_vertex_one (revWord zs) (f * RelLetter.listVal ws) a] at h
  have hrev := vertex_revWord zs (f * RelLetter.listVal ws) (zs.length - a)
  rw [show zs.length - (zs.length - a) = a from by omega] at hrev
  have hh' : g * (RelLetter.listVal zs)⁻¹ = hh := by
    rw [← hzv]
    group
  have hfin : vertex (f * RelLetter.listVal ws) (revWord zs) a
      = vertex hh zs (zs.length - a) := by
    rw [hrev, hwv, hh', vertex_eq_mul_vertex_one zs hh (zs.length - a)]
  simpa using h.trans hfin

/-- **A vertex in the last block is a vertex of the third side**, read against
its orientation; the closing relation is what cancels the translation. -/
theorem vertex_triangle_last_side (ws zs ys : List (RelLetter G Λ)) {f g hh : G}
    (hwv : f * RelLetter.listVal ws = g) (hzv : hh * RelLetter.listVal zs = g)
    (hyv : f * RelLetter.listVal ys = hh) {b : ℕ} (hb : b ≤ ys.length) :
    vertex f (ws ++ revWord zs ++ revWord ys) (ws.length + zs.length + b)
      = vertex f ys (ys.length - b) := by
  have hclose : RelLetter.listVal ys
      = RelLetter.listVal ([] : List (RelLetter G Λ)) * RelLetter.listVal ws
        * RelLetter.listVal (revWord zs) := by
    have hy' : RelLetter.listVal ys = f⁻¹ * hh := by rw [← hyv]; group
    have hw' : RelLetter.listVal ws = f⁻¹ * g := by rw [← hwv]; group
    have hz' : RelLetter.listVal (revWord zs) = g⁻¹ * hh := by
      rw [listVal_revWord, ← hzv]
      group
    rw [hy', hw', hz', RelLetter.listVal_nil, one_mul]
    group
  have h := vertex_fourGon_opposite_closed_of_basepoint [] ws (revWord zs) ys f
    hclose (ys.length - b)
  rw [show ys.length - (ys.length - b) = b from by omega] at h
  simp only [List.nil_append, List.length_nil, Nat.zero_add,
    length_revWord] at h
  rw [h, vertex_eq_mul_vertex_one ys f (ys.length - b)]


/-- **A letter in the middle block is a letter of `revWord zs`.** -/
theorem getElem_triangle_mid (ws zs ys : List (RelLetter G Λ)) {n a : ℕ}
    (ha : a < (revWord zs).length) (hna : n = ws.length + a)
    (hn : n < (ws ++ revWord zs ++ revWord ys).length) :
    (ws ++ revWord zs ++ revWord ys)[n]'hn = (revWord zs)[a]'ha := by
  have h := getElem_fourGon_r [] ws (revWord zs) ys ha
    (by simpa using hna) (by simpa using hn)
  simpa using h

/-- **A letter in the last block is a letter of `revWord ys`.** -/
theorem getElem_triangle_last (ws zs ys : List (RelLetter G Λ)) {n b : ℕ}
    (hb : b < (revWord ys).length)
    (hnb : n = ws.length + (revWord zs).length + b)
    (hn : n < (ws ++ revWord zs ++ revWord ys).length) :
    (ws ++ revWord zs ++ revWord ys)[n]'hn = (revWord ys)[b]'hb := by
  have h := getElem_fourGon_revs [] ws (revWord zs) ys hb
    (by simpa using hnb) (by simpa using hn)
  simpa using h

/-- **The triangle's length.** -/
theorem length_triangle (ws zs ys : List (RelLetter G Λ)) :
    (ws ++ revWord zs ++ revWord ys).length
      = ws.length + zs.length + ys.length := by
  rw [List.length_append, List.length_append, length_revWord, length_revWord]

end OsinComponents
end GGT
end GroupApproximation
