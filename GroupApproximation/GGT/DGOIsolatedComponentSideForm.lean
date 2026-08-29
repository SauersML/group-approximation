import GroupApproximation.GGT.DGOIsolatedComponentRotateCut
import GroupApproximation.GGT.DGOIsolatedComponentCollapseCut
import GroupApproximation.GGT.DGOIsolatedComponentStraddle

/-!
# From the base case at side `0` to the side form at side `t`

Dahmani--Guirardel--Osin's Lemma 4.16 is proved with the distinguished component
as the *first* side and a *single letter*: `c 0 = 0`, `c 1 = 1`,
`IsComp lam w 0 1`.  The recut of `DGOIsolatedComponentStraddle` delivers it as
the side `t`, of whatever length the run had.  This module closes that distance,
and it is the last step of the §4.2 chain that is not geometry:

    base case at side 0, one letter  ⟹  side form at side t, any length

by rotating the closed polygon so that side `t` comes first
(`DGOIsolatedComponentRotate`, `…RotateCut`) and then collapsing that side to the
single letter of its span (`DGOIsolatedComponentNormalise`, `…CollapseCut`).
Both moves keep the span *exactly* — it is the same group element throughout, so
no `d̂_lam` estimate is transported — and both keep isolation.

Composed with `span_mem_relBall_of_sideForm_straddle`, this gives Osin's Lemma 4.2
form for an arbitrary isolated component of a `(μ,b)`-quasi-geodesic `n`-gon from
the base case alone: `isolatedComponent_span_of_baseCase`.

## What the base case must deliver, exactly

For `isolatedComponent_span_of_baseCase` the base case is one binder, and it is
the following, verbatim — a matching statement plugs in with no adapter:

    ∀ (N : ℕ), N ≤ 6 → ∀ (v : G) (w : List (RelLetter G Λ)) (c : ℕ → ℕ),
      (∀ a ∈ w, D.IsLetter a) → RelLetter.listVal w = 1 → c 0 = 0 → c 1 = 1 →
      c N = w.length → (∀ s : ℕ, c s ≤ c (s + 1)) → ∀ lam : Λ,
      (∀ s : ℕ, s < N → s ≠ 0 → ∀ p q : ℕ, c s ≤ p → p ≤ q →
        q ≤ c (s + 1) → ((q - p : ℕ) : ℝ) / mu - b
          ≤ ((wordDist D.alphabet.carrier (vertex v w p)
              (vertex v w q) : ℕ) : ℝ)) →
      IsComp lam w 0 1 → IsIsolated D.fam lam v w 0 →
        (vertex v w 0)⁻¹ * vertex v w 1 ∈ D.relBall lam (C * N)

Five things in it are load-bearing, and each is there for a reason recorded
elsewhere in this chain.

*`N ≤ 6`, not `4`.*  The recut of an `n`-gon yields `n + 2 - (t' - t)` sides, and
the worst case is a component strictly inside one side, which is the case that
actually occurs: `n = 4` gives `6`.  A base case at `4` covers only components
that are whole sides.

*`c 1 = 1`.*  The distinguished side is a single letter.  This is not something
the base case can derive once side `0` is exempt from the clause — deriving it
was what `GeodesicFourGon.isComp_side_succ` did from geodesicity — so it is an
input, and it is what the collapse of `DGOIsolatedComponentNormalise` produces.

*The clause on `s ≠ 0` only.*  Dahmani--Guirardel--Osin's Definition 4.13.  With
the clause on every side the statement is false for a run straddling a corner,
since all of a run's vertices are within one letter of each other.

*`IsComp lam w 0 1` and `IsIsolated D.fam lam v w 0`*, both at index `0`, not at
a general `t`: the rotation is what moves the component there, and it is done on
this side of the interface.

*`C` outside every quantifier*, so that it does not depend on `N`, the word, or
the component; `C * N` is the conclusion, and the caller may weaken it.

A statement phrased with geodesic chains instead of the clause — as
`GeodesicFourGon.geodesic` is, at `(μ,b) = (1,0)` — is equivalent to this one, and
converting is a short lemma in each direction: the clause is the lower half of
`IsGeodesicChain` verbatim, and the upper half is `wordDist_vertex_le'`, which is
automatic.  Say which shape is wanted and it will be supplied here rather than
duplicated on both sides.

## The two degenerate cases, which are where the work is

*The component is the whole closed word* (`c t = 0` and `c (t+1) = w.length`).
Then its span is `v⁻¹ * v = 1`, which lies in every relative ball, and no
rotation happens.  This case has to be taken first, because it is exactly the
case in which the rotation's hypothesis `hwrap` is false: the letter at `0` is a
`lam`-letter of the component itself.

*The component starts at the basepoint but does not fill the word* (`c t = 0`,
`c (t+1) < w.length`).  Then `hwrap` holds vacuously.  Only when `c t > 0` is
`notMem_wrap_of_isIsolated` used, and it is there that closedness plus isolation
rule out a run continuing past the basepoint.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## The transfer -/

/-- **The side form follows from the base case at side `0`.**

The hypothesis is Lemma 4.16 in the shape it is proved: distinguished component
the first side, a single letter (`c 1 = 1`), the quasi-geodesic clause asked only
of the sides `s ≠ 0`.  The conclusion is the same statement with the component at
an arbitrary side `t`, of arbitrary length — which is what the recut produces. -/
theorem sideForm_of_baseCase (D : RelGenSet G Λ) (mu b : ℝ) (C : ℕ)
    (hbase : ∀ (N : ℕ), N ≤ 6 → ∀ (v : G) (w : List (RelLetter G Λ)) (c : ℕ → ℕ),
      (∀ a ∈ w, D.IsLetter a) → RelLetter.listVal w = 1 → c 0 = 0 → c 1 = 1 →
      c N = w.length → (∀ s : ℕ, c s ≤ c (s + 1)) → ∀ lam : Λ,
      (∀ s : ℕ, s < N → s ≠ 0 → ∀ p q : ℕ, c s ≤ p → p ≤ q →
        q ≤ c (s + 1) → ((q - p : ℕ) : ℝ) / mu - b
          ≤ ((wordDist D.alphabet.carrier (vertex v w p)
              (vertex v w q) : ℕ) : ℝ)) →
      IsComp lam w 0 1 → IsIsolated D.fam lam v w 0 →
        (vertex v w 0)⁻¹ * vertex v w 1 ∈ D.relBall lam (C * N)) :
    ∀ (N : ℕ), N ≤ 6 → ∀ (v : G) (w : List (RelLetter G Λ)) (c : ℕ → ℕ),
      (∀ a ∈ w, D.IsLetter a) → RelLetter.listVal w = 1 → c 0 = 0 →
      c N = w.length → (∀ s : ℕ, c s ≤ c (s + 1)) → ∀ (lam : Λ) (t : ℕ), t < N →
      (∀ s : ℕ, s < N → s ≠ t → ∀ p q : ℕ, c s ≤ p → p ≤ q →
        q ≤ c (s + 1) → ((q - p : ℕ) : ℝ) / mu - b
          ≤ ((wordDist D.alphabet.carrier (vertex v w p)
              (vertex v w q) : ℕ) : ℝ)) →
      IsComp lam w (c t) (c (t + 1)) → IsIsolated D.fam lam v w (c t) →
        (vertex v w (c t))⁻¹ * vertex v w (c (t + 1))
          ∈ D.relBall lam (C * N) := by
  intro N hN v w c hlet hclosed hc0 hcN hcmono lam t ht hcqg hcomp hiso
  have hik : c t < c (t + 1) := hcomp.1
  have hkw : c (t + 1) ≤ w.length := hcomp.2.1
  have hiw : c t ≤ w.length := by omega
  have hzfam : (vertex v w (c t))⁻¹ * vertex v w (c (t + 1)) ∈ D.fam lam :=
    span_mem_fam_of_isComp D v hlet hcomp
  -- the component filling the whole closed word has trivial span
  by_cases hwhole : c t = 0 ∧ c (t + 1) = w.length
  · obtain ⟨hi0, hkl⟩ := hwhole
    have hone : (vertex v w (c t))⁻¹ * vertex v w (c (t + 1)) = 1 := by
      rw [hi0, hkl, vertex_zero, vertex_length_of_closed v w hclosed,
        inv_mul_cancel]
    rw [hone]
    exact one_mem_relBall D lam _
  -- otherwise the run does not continue past the basepoint
  have hwrap : ∀ h0 : 0 < w.length, c (t + 1) = w.length →
      ¬ (w[0]'h0).IsCompOf lam := by
    rcases Nat.eq_zero_or_pos (c t) with hi0 | hipos
    · intro _ hkl
      exact absurd ⟨hi0, hkl⟩ hwhole
    · exact notMem_wrap_of_isIsolated D lam v hlet hclosed hcomp hiso hipos
  -- 1.  rotate, so that the component is the first side
  obtain ⟨d, hd0, hd1, hdN, hdmono, hdqg⟩ :=
    exists_rot_cut D mu b hclosed hc0 hcN hcmono ht hcqg
  have hrlet := letters_rotWord D hlet (c t)
  have hrclosed := listVal_rotWord w (c t) hclosed
  have hrcomp : IsComp lam (rotWord w (c t)) 0 (c (t + 1) - c t) :=
    isComp_rotWord lam hcomp hiw hwrap
  have hriso : IsIsolated D.fam lam (vertex v w (c t)) (rotWord w (c t)) 0 :=
    isIsolated_rotWord D lam v hlet hclosed hcomp hiso hwrap
  -- the two vertices of the rotated first side are the two ends of the component
  have hv0 : vertex (vertex v w (c t)) (rotWord w (c t)) 0 = vertex v w (c t) := by
    rw [vertex_rotWord_le v w hiw 0 (Nat.zero_le _), Nat.add_zero]
  have hvK : vertex (vertex v w (c t)) (rotWord w (c t)) (c (t + 1) - c t)
      = vertex v w (c (t + 1)) := by
    rw [vertex_rotWord_le v w hiw (c (t + 1) - c t) (by omega),
      show c t + (c (t + 1) - c t) = c (t + 1) from by omega]
  have hspan : vertex (vertex v w (c t)) (rotWord w (c t)) 0 *
      ((vertex v w (c t))⁻¹ * vertex v w (c (t + 1)))
      = vertex (vertex v w (c t)) (rotWord w (c t)) (c (t + 1) - c t) := by
    rw [hv0, hvK, mul_inv_cancel_left]
  -- 2.  collapse that side to the single letter of its span
  obtain ⟨e, he0, he1, heN, hemono, heqg⟩ :=
    exists_collapse_cut D mu b (c := d) (lam := lam)
      (s := (vertex v w (c t))⁻¹ * vertex v w (c (t + 1))) hd1 hdN hdmono
      (by omega) (by omega) hspan hdqg
  have hclet := letters_normWord D hrlet lam 0 (c (t + 1) - c t) hzfam
  have hcclosed : RelLetter.listVal (normWord (rotWord w (c t)) lam 0
      (c (t + 1) - c t) ((vertex v w (c t))⁻¹ * vertex v w (c (t + 1)))) = 1 := by
    have hz' : RelLetter.listVal ((rotWord w (c t)).take (c (t + 1) - c t))
        = (vertex v w (c t))⁻¹ * vertex v w (c (t + 1)) := by
      have h := vertex_eq_mul_listVal_take (rotWord w (c t)) (vertex v w (c t))
        (c (t + 1) - c t)
      rw [hvK] at h
      rw [h, inv_mul_cancel_left]
    have hnorm := listVal_normWord (rotWord w (c t)) lam
      (Nat.zero_le (c (t + 1) - c t))
    rw [List.drop_zero, Nat.sub_zero, hz', hrclosed] at hnorm
    exact hnorm
  have hccomp := isComp_normWord (rotWord w (c t)) lam
    ((vertex v w (c t))⁻¹ * vertex v w (c (t + 1))) hrcomp
  have hciso := isIsolated_normWord D (vertex v w (c t))
    ((vertex v w (c t))⁻¹ * vertex v w (c (t + 1))) hrcomp hspan hriso
  -- 3.  the base case, and the two vertices it returns
  have hgoal := hbase N hN (vertex v w (c t))
    (normWord (rotWord w (c t)) lam 0 (c (t + 1) - c t)
      ((vertex v w (c t))⁻¹ * vertex v w (c (t + 1)))) e hclet hcclosed he0 he1
    heN hemono lam heqg hccomp hciso
  have hw0 : vertex (vertex v w (c t))
      (normWord (rotWord w (c t)) lam 0 (c (t + 1) - c t)
        ((vertex v w (c t))⁻¹ * vertex v w (c (t + 1)))) 0
      = vertex v w (c t) := by
    rw [vertex_normWord_le (vertex v w (c t)) (rotWord w (c t)) lam 0
      (c (t + 1) - c t) _ (Nat.zero_le _) 0 le_rfl, hv0]
  have hw1 : vertex (vertex v w (c t))
      (normWord (rotWord w (c t)) lam 0 (c (t + 1) - c t)
        ((vertex v w (c t))⁻¹ * vertex v w (c (t + 1)))) 1
      = vertex v w (c (t + 1)) := by
    rw [vertex_normWord_add (vertex v w (c t)) (rotWord w (c t)) lam 0
      (c (t + 1) - c t) _ (Nat.zero_le _) hspan 1 0 (by omega), Nat.add_zero, hvK]
  rw [hw0, hw1] at hgoal
  exact hgoal

/-! ## The whole chain, in one statement -/

/-- **Osin's Lemma 4.2 form, from the base case alone.**

The first binder is Dahmani--Guirardel--Osin's Lemma 4.16 in the shape it is
proved — distinguished component the first side, a single letter, the clause on
the other sides only.  The conclusion is the bound for an *arbitrary* isolated
component of a `(μ,b)`-quasi-geodesic `n`-gon, `n ≤ 4`: no hypothesis on where the
component sits, no requirement that it be a side or a single letter, and no
constant lost beyond the `n ↦ n + 2` of the recut.

The chain is `span_mem_relBall_of_sideForm_straddle ∘ sideForm_of_baseCase`:
recut the polygon so the component is a side (exempt from the clause, which is
what makes a straddling run harmless), turn it round so that side comes first,
collapse it to the single letter of its span, and quote the base case.  The span
is the same group element at every step. -/
theorem isolatedComponent_span_of_baseCase (D : RelGenSet G Λ) (mu b : ℝ) (C : ℕ)
    (hbase : ∀ (N : ℕ), N ≤ 6 → ∀ (v : G) (w : List (RelLetter G Λ)) (c : ℕ → ℕ),
      (∀ a ∈ w, D.IsLetter a) → RelLetter.listVal w = 1 → c 0 = 0 → c 1 = 1 →
      c N = w.length → (∀ s : ℕ, c s ≤ c (s + 1)) → ∀ lam : Λ,
      (∀ s : ℕ, s < N → s ≠ 0 → ∀ p q : ℕ, c s ≤ p → p ≤ q →
        q ≤ c (s + 1) → ((q - p : ℕ) : ℝ) / mu - b
          ≤ ((wordDist D.alphabet.carrier (vertex v w p)
              (vertex v w q) : ℕ) : ℝ)) →
      IsComp lam w 0 1 → IsIsolated D.fam lam v w 0 →
        (vertex v w 0)⁻¹ * vertex v w 1 ∈ D.relBall lam (C * N))
    {n : ℕ} (hn : n ≤ 4) {v : G} {w : List (RelLetter G Λ)} {c : ℕ → ℕ}
    (hlet : ∀ a ∈ w, D.IsLetter a) (hclosed : RelLetter.listVal w = 1)
    (hc0 : c 0 = 0) (hcn : c n = w.length) (hcmono : ∀ s : ℕ, c s ≤ c (s + 1))
    (hcqg : ∀ s : ℕ, s < n → ∀ p q : ℕ, c s ≤ p → p ≤ q → q ≤ c (s + 1) →
      ((q - p : ℕ) : ℝ) / mu - b
        ≤ ((wordDist D.alphabet.carrier (vertex v w p) (vertex v w q) : ℕ) : ℝ))
    {lam : Λ} {i k t t' : ℕ} (ht : t < n) (hti : c t ≤ i) (hit : i ≤ c (t + 1))
    (ht' : t' < n) (htk : c t' ≤ k) (hkt' : k ≤ c (t' + 1)) (htt' : t ≤ t')
    (hcomp : IsComp lam w i k) (hiso : IsIsolated D.fam lam v w i) :
    (vertex v w i)⁻¹ * vertex v w k ∈ D.relBall lam (C * (n + 2)) :=
  span_mem_relBall_of_sideForm_straddle D mu b C
    (sideForm_of_baseCase D mu b C hbase) hn hlet hclosed hc0 hcn hcmono hcqg ht
    hti hit ht' htk hkt' htt' hcomp hiso

end OsinComponents
end GGT
end GroupApproximation
