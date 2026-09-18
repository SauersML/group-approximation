import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.GFaceWindSel
import GroupApproximation.Meta.AxiomGuard

/-!
# Winding choice of `F'`: positivity on a lobe side from the absence of sink regions

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-80.

Map-level lemmas for `Piece10Live/GFaceWindSelPfStatement`. They reduce positivity of `g` on
the side `S` of a lobe (the conclusion of `gfaceWindSel_Statement`) to a `g`-free planar fact.

## The winding decomposition

Let `c = W ++ T` (cyclically), where `W` is a simple closed walk with side `S`. Put
`g = ind_S + h`. Then `h` is cobounded by `T`, and it is continuous across `W`, because the
edges of `W` are not edges of `T`. For a dart `d` of `W` the coboundary gives
`g (faceOf d) = g (faceOf (alpha d)) + 1 ≥ 1` (`gfaceWindSelPf_face_pos`, for every dart of
`c`). Inside `S`, `g` changes only across darts of `T`.

## The sink region

Take the zero set `K₀ = {f ∈ S | g f ≤ 0}` (`gfaceWindSelPf_zero`). It is a **sink region of
`c` in `S`** (`gfaceWindSelPf_Sink`, proved in `gfaceWindSelPf_zero_sink`):
* `K ⊆ S`;
* no dart of `c` lies on a face of `K`;
* every boundary dart `e` of `K` (face in `K`, opposite face not in `K`) has `alpha e ∈ c`.

In words, `c` runs around `K` with `K` on its right, and it never enters `K`. The definition
mentions neither `g` nor `o`. So `g ≥ 1` on `S` follows once every sink region of `c` in `S` is
empty (`gfaceWindSelPf_pos_of_sink`).

## A constructive sufficient condition

The relation `gfaceWindSelPf_Up M c a b` steps across a dart `e` from `faceOf (alpha e)` to
`faceOf e`, whenever `alpha e ∉ c`. Along such a step `g` never decreases.
Suppose every face of `S` is reachable by `Up`-steps from the face of some dart of `c`. Then
every sink region in `S` is empty (`gfaceWindSelPf_sink_empty_of_reach`).

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind

universe v

open scoped Classical

/-- **A sink region of `c` in `S`**: a face set `K ⊆ S`, with no dart of `c` on its faces,
whose every boundary dart `e` has its reverse `alpha e` on `c`. -/
def gfaceWindSelPf_Sink (M : CombMap.{v}) (S : Finset M.Face) (c : List M.Dart)
    (K : Finset M.Face) : Prop :=
  K ⊆ S ∧ (∀ e : M.Dart, M.faceOf e ∈ K → e ∉ c) ∧
    ∀ e : M.Dart, M.faceOf e ∈ K → M.faceOf (M.alpha e) ∉ K → M.alpha e ∈ c

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindSelPf_Sink

/-- The zero set of `g` on `S`. -/
noncomputable def gfaceWindSelPf_zero {M : CombMap.{v}} (S : Finset M.Face)
    (g : M.Face → ℤ) : Finset M.Face :=
  S.filter fun f => g f ≤ 0

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindSelPf_zero

theorem gfaceWindSelPf_mem_zero {M : CombMap.{v}} {S : Finset M.Face} {g : M.Face → ℤ}
    {f : M.Face} : f ∈ gfaceWindSelPf_zero S g ↔ f ∈ S ∧ g f ≤ 0 := by
  simp only [gfaceWindSelPf_zero, Finset.mem_filter]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindSelPf_mem_zero

/-- **`g ≥ 1` on the face of a dart of `c`**: a nonnegative face function cobounded by `c`,
where no dart of `c` has its reverse on `c`, is at least `1` on the face of each dart of `c`. -/
theorem gfaceWindSelPf_face_pos {M : CombMap.{v}} {c : List M.Dart} {g : M.Face → ℤ}
    (hcob : ∀ d, g (M.faceOf d) - g (M.faceOf (M.alpha d)) =
      gfaceWind_lind c d - gfaceWind_lind c (M.alpha d))
    (hal : ∀ x ∈ c, M.alpha x ∉ c) (hpos : ∀ f, 0 ≤ g f) {d : M.Dart} (hd : d ∈ c) :
    1 ≤ g (M.faceOf d) := by
  linarith [hcob d, gfaceWind_lind_pos hd, gfaceWind_lind_neg (hal d hd),
    hpos (M.faceOf (M.alpha d))]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindSelPf_face_pos

/-- **The zero set is a sink region**: if the boundary darts of `S` lie on `c`, then the faces
of `S` where `g ≤ 0` form a sink region of `c` in `S`. -/
theorem gfaceWindSelPf_zero_sink {M : CombMap.{v}} {c : List M.Dart} {g : M.Face → ℤ}
    {S : Finset M.Face}
    (hcob : ∀ d, g (M.faceOf d) - g (M.faceOf (M.alpha d)) =
      gfaceWind_lind c d - gfaceWind_lind c (M.alpha d))
    (hal : ∀ x ∈ c, M.alpha x ∉ c) (hpos : ∀ f, 0 ≤ g f)
    (hbd : ∀ e : M.Dart, M.faceOf e ∈ S → M.faceOf (M.alpha e) ∉ S → e ∈ c) :
    gfaceWindSelPf_Sink M S c (gfaceWindSelPf_zero S g) := by
  have hnc : ∀ e : M.Dart, M.faceOf e ∈ gfaceWindSelPf_zero S g → e ∉ c := by
    intro e he hec
    have h0 := (gfaceWindSelPf_mem_zero.mp he).2
    linarith [gfaceWindSelPf_face_pos hcob hal hpos hec]
  refine ⟨fun f hf => (gfaceWindSelPf_mem_zero.mp hf).1, hnc, ?_⟩
  intro e he hae
  have hS : M.faceOf e ∈ S := (gfaceWindSelPf_mem_zero.mp he).1
  have h0 : g (M.faceOf e) ≤ 0 := (gfaceWindSelPf_mem_zero.mp he).2
  have hae' : M.faceOf (M.alpha e) ∈ S := by
    by_contra hn
    exact hnc e he (hbd e hS hn)
  have h1 : ¬ g (M.faceOf (M.alpha e)) ≤ 0 := fun h =>
    hae (gfaceWindSelPf_mem_zero.mpr ⟨hae', h⟩)
  by_contra hn
  linarith [hcob e, gfaceWind_lind_neg (hnc e he), gfaceWind_lind_neg hn, not_le.mp h1]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindSelPf_zero_sink

/-- **Positivity from the absence of sink regions**: if every sink region of `c` in `S` is
empty, then `g ≥ 1` on `S` (the zero set is such a region). -/
theorem gfaceWindSelPf_pos_of_sink {M : CombMap.{v}} {c : List M.Dart} {g : M.Face → ℤ}
    {S : Finset M.Face}
    (hcob : ∀ d, g (M.faceOf d) - g (M.faceOf (M.alpha d)) =
      gfaceWind_lind c d - gfaceWind_lind c (M.alpha d))
    (hal : ∀ x ∈ c, M.alpha x ∉ c) (hpos : ∀ f, 0 ≤ g f)
    (hbd : ∀ e : M.Dart, M.faceOf e ∈ S → M.faceOf (M.alpha e) ∉ S → e ∈ c)
    (hK : ∀ K : Finset M.Face, gfaceWindSelPf_Sink M S c K → K = ∅) :
    ∀ f ∈ S, 1 ≤ g f := by
  intro f hf
  by_contra hlt
  have hmem : f ∈ gfaceWindSelPf_zero S g := gfaceWindSelPf_mem_zero.mpr ⟨hf, by omega⟩
  rw [hK _ (gfaceWindSelPf_zero_sink hcob hal hpos hbd)] at hmem
  exact Finset.notMem_empty f hmem

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindSelPf_pos_of_sink

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind
