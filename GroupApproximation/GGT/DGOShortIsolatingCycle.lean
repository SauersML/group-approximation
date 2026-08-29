import GroupApproximation.GGT.DGOPolygonGeodesicChain

/-!
# Corners, lengths and isolation for Dahmani--Guirardel--Osin's Lemma 4.16

The lemma builds, from a `(1,0)`-quasi-geodesic 4-gon carrying an isolated
`H lam`-component as its first side, a **closed** admissible word of bounded
length in which that component is still isolated; feeding that to
`relBall_of_isolated_of_closed` is what bounds `d̂_lam` of the span.  This module
supplies the four facts the construction runs on, before the construction.

## Corners

`GeodesicFourGon.side_dist` says a side realises the gap between its corners,
which is the geodesic clause read at the two ends, and
`GeodesicFourGon.vertex_last` says the fourth corner is the basepoint, which is
closedness.  Together they turn statements about corner distances into
statements about the cut function, where `omega` can see them.

## The short case, where no construction is needed

`length_le_of_corners_close` is Dahmani--Guirardel--Osin's opening move in their
Case 4: when both corners flanking the component are within `θ + 1` of it, the
polygon is *already* short and serves as its own cycle.  The far side is bounded
through the other three, `d(x₃,x₄) ≤ d(x₃,x₂) + d(x₂,x₁) + d(x₁,x₄)`, and
`d(x₁,x₂) ≤ 1` because the component's span is a single letter of the alphabet.
This is why the construction only ever has to handle a corner that is *far*.

## Isolation, once, for every case

`isIsolated_zero_of_notMem` reduces `IsIsolated` at index `0` to a statement
with no components in it: no `lam`-letter of the cycle away from `0` is read at
a vertex of the coset of the basepoint.  Every case of the construction
discharges that the same way --- polygon vertices by
`notMem_coset_of_isIsolated`, connector vertices by
`notMem_coset_vertex_of_offset` --- so the case analysis never reasons about
component *starts* again.  `notMem_coset_of_isIsolated_zero` is the polygon half
of that, specialised to a component that is the first letter.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## Corners -/

/-- **A non-exempt side realises the gap between its corners.**  Side `0` is
exempt from the geodesic clause, so it is excluded: the distinguished component
may be a long run whose ends are one alphabet letter apart. -/
theorem GeodesicFourGon.side_dist (D : RelGenSet G Λ) {v : G}
    {w : List (RelLetter G Λ)} {c : ℕ → ℕ} (hQ : GeodesicFourGon D v w c)
    {t : ℕ} (ht : t < 4) (ht0 : t ≠ 0) :
    wordDist D.alphabet.carrier (vertex v w (c t)) (vertex v w (c (t + 1)))
      = c (t + 1) - c t := by
  have hcs : c t ≤ c (t + 1) := hQ.mono (Nat.le_succ t)
  have hEq : c t + (c (t + 1) - c t) = c (t + 1) := by omega
  have h0 : wordDist D.alphabet.carrier (vertex v w (c t + 0))
      (vertex v w (c t + (c (t + 1) - c t))) = c (t + 1) - c t - 0 :=
    hQ.geodesic t ht ht0 0 (c (t + 1) - c t) (Nat.zero_le _) le_rfl
  rw [Nat.add_zero, hEq, Nat.sub_zero] at h0
  exact h0

/-- **The fourth corner is the basepoint**, the path being closed. -/
theorem GeodesicFourGon.vertex_last (D : RelGenSet G Λ) {v : G}
    {w : List (RelLetter G Λ)} {c : ℕ → ℕ} (hQ : GeodesicFourGon D v w c) :
    vertex v w (c 4) = v := by
  rw [hQ.finish, vertex_eq_mul_listVal_take, List.take_length, hQ.closed, mul_one]

/-! ## The short case -/

/-- **When both corners flanking the component are close, the polygon is already
short.**  The far side is bounded through the other three, using that the
component's span is one letter of the alphabet, so `d(x₁,x₂) ≤ 1`.

The distinguished side is exempt from the geodesic clause, so its length `c 1`
is not bounded by the distance between its ends and has to be supplied: `hc01`
says the component has already been collapsed to a single letter, which
`DGOIsolatedComponentNormalise.normWord` arranges. -/
theorem GeodesicFourGon.length_le_of_corners_close (D : RelGenSet G Λ) {v : G}
    {w : List (RelLetter G Λ)} {c : ℕ → ℕ} (hQ : GeodesicFourGon D v w c)
    {lam : Λ} (hcomp : IsComp lam w (c 0) (c 1)) (hc01 : c 1 = c 0 + 1) {θ : ℕ}
    (h12 : c 2 - c 1 ≤ θ + 1) (h34 : c 4 - c 3 ≤ θ + 1) :
    w.length ≤ 4 * θ + 6 := by
  have hsymm := D.alphabet.symmetricGenerating
  have hst : c 0 = 0 := hQ.start
  have hlen : w.length = c 4 := hQ.finish.symm
  have hm0 : c 0 ≤ c 1 := hQ.mono (by omega : (0 : ℕ) ≤ 1)
  have hm1 : c 1 ≤ c 2 := hQ.mono (by omega : (1 : ℕ) ≤ 2)
  have hm2 : c 2 ≤ c 3 := hQ.mono (by omega : (2 : ℕ) ≤ 3)
  have hm3 : c 3 ≤ c 4 := hQ.mono (by omega : (3 : ℕ) ≤ 4)
  have hclose : vertex v w (c 4) = vertex v w (c 0) := by
    rw [hQ.vertex_last D, hst, vertex_zero]
  have hd01 : wordDist D.alphabet.carrier (vertex v w (c 0)) (vertex v w (c 1))
      ≤ 1 :=
    wordDist_le_one_of_mem_fam D (span_mem_fam_of_isComp D v hQ.letters hcomp)
  have hs1 : wordDist D.alphabet.carrier (vertex v w (c 1)) (vertex v w (c 2))
      = c 2 - c 1 := hQ.side_dist D (by omega : (1 : ℕ) < 4) (by omega)
  have hs2 : wordDist D.alphabet.carrier (vertex v w (c 2)) (vertex v w (c 3))
      = c 3 - c 2 := hQ.side_dist D (by omega : (2 : ℕ) < 4) (by omega)
  have hs3 : wordDist D.alphabet.carrier (vertex v w (c 3)) (vertex v w (c 4))
      = c 4 - c 3 := hQ.side_dist D (by omega : (3 : ℕ) < 4) (by omega)
  rw [hclose] at hs3
  have hc21 : wordDist D.alphabet.carrier (vertex v w (c 2)) (vertex v w (c 1))
      = wordDist D.alphabet.carrier (vertex v w (c 1)) (vertex v w (c 2)) :=
    wordDist_comm hsymm _ _
  have hc10 : wordDist D.alphabet.carrier (vertex v w (c 1)) (vertex v w (c 0))
      = wordDist D.alphabet.carrier (vertex v w (c 0)) (vertex v w (c 1)) :=
    wordDist_comm hsymm _ _
  have hc03 : wordDist D.alphabet.carrier (vertex v w (c 0)) (vertex v w (c 3))
      = wordDist D.alphabet.carrier (vertex v w (c 3)) (vertex v w (c 0)) :=
    wordDist_comm hsymm _ _
  have ht1 := wordDist_triangle hsymm (vertex v w (c 2)) (vertex v w (c 1))
    (vertex v w (c 3))
  have ht2 := wordDist_triangle hsymm (vertex v w (c 1)) (vertex v w (c 0))
    (vertex v w (c 3))
  omega

/-! ## Isolation, reduced to a statement about letters -/

/-- **Isolation of the component at `0`, with the components taken out.**  What
has to be checked is only that no `lam`-letter away from `0` is read at a vertex
of the coset of the basepoint. -/
theorem isIsolated_zero_of_notMem (D : RelGenSet G Λ) (lam : Λ) (u : G)
    {q : List (RelLetter G Λ)} {k : ℕ} (hcomp : IsComp lam q 0 k)
    (h : ∀ j : ℕ, j ≠ 0 → ∀ hj : j < q.length, (q[j]'hj).IsCompOf lam →
      u⁻¹ * vertex u q j ∉ D.fam lam) :
    IsIsolated D.fam lam u q 0 := by
  refine ⟨⟨k, hcomp⟩, ?_⟩
  rintro j hne ⟨k', hc'⟩ hconn
  have hjk : j < k' := hc'.1
  have hkq : k' ≤ q.length := hc'.2.1
  have hjq : j < q.length := by omega
  have hcj : (q[j]'hjq).IsCompOf lam := hc'.2.2.1 j le_rfl hjk hjq
  refine h j hne hjq hcj ?_
  have hmem : (vertex u q 0)⁻¹ * vertex u q j ∈ D.fam lam := hconn
  rwa [vertex_zero] at hmem

/-- **What isolation forbids, for a component that is the first letter.** -/
theorem notMem_coset_of_isIsolated_zero (D : RelGenSet G Λ) (lam : Λ) (v : G)
    {w : List (RelLetter G Λ)} (hlet : ∀ a ∈ w, D.IsLetter a)
    (hcomp : IsComp lam w 0 1) (hiso : IsIsolated D.fam lam v w 0)
    {p : ℕ} (hp : p < w.length) (hcp : (w[p]'hp).IsCompOf lam) (hp1 : 1 ≤ p) :
    v⁻¹ * vertex v w p ∉ D.fam lam := by
  intro hmem
  refine notMem_coset_of_isIsolated D lam v hlet hcomp hiso hp hcp (Or.inr hp1) ?_
  show (vertex v w 0)⁻¹ * vertex v w p ∈ D.fam lam
  rwa [vertex_zero]

end OsinComponents
end GGT
end GroupApproximation
