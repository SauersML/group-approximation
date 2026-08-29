import GroupApproximation.GGT.DGOReversedSplice
import GroupApproximation.GGT.DGOIsolatedComponentNormalise

/-!
# Dahmani--Guirardel--Osin's Lemma 4.16 at `mu = 1`, `b = 0`, `n = 4`

From a 4-gon carrying an isolated `H lam`-component as its distinguished side,
this module builds a **closed** admissible word of length at most
`100 (delta + 1)` in which that component is still isolated.  Feeding it to
`relBall_of_isolated_of_closed` is what bounds `d_lam` of the span, and that
composition is `DGOIsolatedComponentBoundFourGon`.

Everything below is at `mu = 1`, `b = 0`, where a non-exempt side of the polygon
is a geodesic chain and the thinness constant is `10 delta` with no
quasi-geodesic stability theorem.  Side `0` --- the distinguished one --- is
exempt, as in Dahmani--Guirardel--Osin's Definition 4.13.

## The two constants

`theta = 10 delta` is the thinness constant of `exists_index_close_side_one` and
`exists_index_close_side_three`.  The **offset** is `theta + 3` along the side,
not `theta + 2`: the coset being avoided is centred at the basepoint `v`, and
the two ends of the distinguished side are one alphabet letter apart, so an
offset of `theta + 3` measured from the corner `vertex v w (c 1)` yields only
`theta + 2` from `v`, which is what `notMem_coset_of_offset` needs.  This is the
off-by-one that "changing the enumeration of the sides" hides in the printed
proof.

## The case tree, and the length in each branch

Write `L1 = c 2 - c 1` and `L3 = c 4 - c 3` for the two sides flanking the
component.  Once the run has been collapsed to one letter, `c 1 = 1`.

* **Both flanks short** (`L1, L3 <= theta + 2`).  No construction: the polygon
  is already its own cycle.  `length_le_of_corners_close` at `theta + 1` bounds
  the far side through the other three, giving
  `|w| <= 4 (theta + 1) + 6 = 4 theta + 10`.
* **Side 1 long, side 3 short.**  Offset to `m = c 1 + (theta + 3)`; thinness at
  `m` lands on side 2 or side 3 (the exempt alternative is discarded by the
  offset count).  On side 3 the tail is at most `L3 <= theta + 2`.  On side 2 the
  near vertex is within `2 theta + 4` of `v` and `x3` is within `theta + 2`, so
  the geodesic side 2 gives `c 3 - p <= 3 theta + 6` and the tail is at most
  `4 theta + 8`.  One connector: `m + theta + tail <= 6 theta + 12`.
* **Side 3 long, side 1 short.**  The mirror, with the backward offset
  `j = c 4 - (theta + 3)`; `6 theta + 12` again.
* **Both long.**  Two offsets.  If either near vertex falls on the *far* side
  the branch collapses to one connector (`4 theta + 8`).  Otherwise both near
  vertices are on side 2, each within `2 theta + 4` of `v`, so --- side 2 being
  geodesic --- they are at most `4 theta + 7` apart.  If they do not interleave,
  `cycle_of_two_connectors`; if they do, `cycle_of_reversed_splice`.  Either way
  `m + theta + (gap) + theta + (theta + 3) <= 8 theta + 14`.

The worst branch is `8 theta + 14 = 80 delta + 14`, and
`80 delta + 14 <= 100 delta + 100 = 100 (delta + 1)`.  No branch is sharp and
nothing downstream needs one: Osin's Lemma 4.2 quantifies the constant
existentially.

## Collapsing first

The exempt side may be a run of many `lam`-letters, and every splice in
`DGOCycleAssembly`, `DGOTwoConnectorSplice` and `DGOReversedSplice` assumes the
distinguished component is the *first letter* of the polygon.
`exists_unit_side_zero` performs Dahmani--Guirardel--Osin's normalisation once,
through `DGOIsolatedComponentNormalise.normWord`: the run is replaced by the
single `lam`-letter it spans, which changes neither the span nor isolatedness,
and the three non-exempt sides are carried across unchanged because the collapse
only removes vertices strictly inside the run.  After it, `c 1 = 1` and the case
tree can run.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## Collapsing the exempt side to one letter -/

/-- **The distinguished side may be normalised to a single letter.**

`normWord` replaces the run `[c 0, c 1)` by the one `lam`-letter it spans.  The
collapsed word is again a 4-gon with the same three non-exempt sides --- their
vertices are vertices of `w` shifted by the length the collapse removed, and the
word metric does not see the shift --- carrying an isolated component that is
now a single letter with *literally the same span*, so `d_lam` of it is
preserved with nothing to prove.

The cut function is `c' t = 1 + (c t - c 1) - (1 - t)`, which is `0` at `t = 0`
and `1 + (c t - c 1)` afterwards.  It is introduced through its two defining
equations and never unfolded again: the closed form exists only so that no `if`
reaches `omega`, which does not split one. -/
theorem GeodesicFourGon.exists_unit_side_zero (D : RelGenSet G Λ) {v : G}
    {w : List (RelLetter G Λ)} {c : ℕ → ℕ} (hQ : GeodesicFourGon D v w c)
    {lam : Λ} (hcomp : IsComp lam w (c 0) (c 1))
    (hiso : IsIsolated D.fam lam v w (c 0)) :
    ∃ (w' : List (RelLetter G Λ)) (c' : ℕ → ℕ),
      GeodesicFourGon D v w' c' ∧ c' 1 = 1 ∧
        IsComp lam w' 0 1 ∧ IsIsolated D.fam lam v w' 0 ∧
        (vertex v w' 0)⁻¹ * vertex v w' 1
          = (vertex v w (c 0))⁻¹ * vertex v w (c 1) := by
  have hst : c 0 = 0 := hQ.start
  have hfin : c 4 = w.length := hQ.finish
  rw [hst] at hcomp hiso
  have hspan : vertex v w 0 * RelLetter.listVal ((w.drop 0).take (c 1 - 0))
      = vertex v w (c 1) := listVal_segment w v (by omega)
  have hsmem : RelLetter.listVal ((w.drop 0).take (c 1 - 0)) ∈ D.fam lam := by
    have h := span_mem_fam_of_isComp D v hQ.letters hcomp
    rw [← hspan] at h
    rwa [inv_mul_cancel_left] at h
  have hcl' : RelLetter.listVal
      (normWord w lam 0 (c 1) (RelLetter.listVal ((w.drop 0).take (c 1 - 0))))
      = 1 := by
    rw [listVal_normWord w lam (by omega : (0 : ℕ) ≤ c 1)]
    exact hQ.closed
  have hlen' : (normWord w lam 0 (c 1)
      (RelLetter.listVal ((w.drop 0).take (c 1 - 0)))).length
      = 0 + 1 + (w.length - c 1) :=
    length_normWord w lam 0 (c 1) (RelLetter.listVal ((w.drop 0).take (c 1 - 0))) (by omega)
  have hvadd : ∀ t : ℕ, vertex v (normWord w lam 0 (c 1)
      (RelLetter.listVal ((w.drop 0).take (c 1 - 0)))) (1 + t)
      = vertex v w (c 1 + t) := fun t =>
    vertex_normWord_add v w lam 0 (c 1)
      (RelLetter.listVal ((w.drop 0).take (c 1 - 0))) (by omega) hspan (1 + t) t
      (by omega)
  have hv0 : vertex v (normWord w lam 0 (c 1)
      (RelLetter.listVal ((w.drop 0).take (c 1 - 0)))) 0 = vertex v w 0 :=
    vertex_normWord_le v w lam 0 (c 1)
      (RelLetter.listVal ((w.drop 0).take (c 1 - 0))) (by omega) 0 (by omega)
  have hv1 : vertex v (normWord w lam 0 (c 1)
      (RelLetter.listVal ((w.drop 0).take (c 1 - 0)))) 1 = vertex v w (c 1) := by
    have h := hvadd 0
    rwa [Nat.add_zero, Nat.add_zero] at h
  obtain ⟨c', hc'0, hc'pos⟩ :
      ∃ c' : ℕ → ℕ, c' 0 = 0 ∧ ∀ t : ℕ, t ≠ 0 → c' t = 1 + (c t - c 1) := by
    refine ⟨fun t => 1 + (c t - c 1) - (1 - t), ?_, ?_⟩
    · show 1 + (c 0 - c 1) - (1 - 0) = 0
      omega
    · intro t ht
      show 1 + (c t - c 1) - (1 - t) = 1 + (c t - c 1)
      omega
  have hc'1 : c' 1 = 1 := by
    rw [hc'pos 1 (by omega)]
    omega
  refine ⟨normWord w lam 0 (c 1)
    (RelLetter.listVal ((w.drop 0).take (c 1 - 0))), c',
    ⟨letters_normWord D hQ.letters lam 0 (c 1) hsmem, hcl', hc'0, ?_, ?_, ?_⟩,
    hc'1, isComp_normWord w lam (RelLetter.listVal ((w.drop 0).take (c 1 - 0))) hcomp,
    isIsolated_normWord D v (RelLetter.listVal ((w.drop 0).take (c 1 - 0))) hcomp hspan hiso, ?_⟩
  · rw [hc'pos 4 (by omega), hlen']
    omega
  · intro a b hab
    rcases Nat.eq_zero_or_pos a with ha | ha
    · subst ha
      rw [hc'0]
      exact Nat.zero_le _
    · have hb : b ≠ 0 := by omega
      have hcab : c a ≤ c b := hQ.mono hab
      rw [hc'pos a (by omega), hc'pos b hb]
      omega
  · intro t ht ht0 a b hab hbn
    have hct1 : c 1 ≤ c t := hQ.mono (show (1 : ℕ) ≤ t by omega)
    have hct : c t ≤ c (t + 1) := hQ.mono (Nat.le_succ t)
    have hc't : c' t = 1 + (c t - c 1) := hc'pos t ht0
    have hc't1 : c' (t + 1) = 1 + (c (t + 1) - c 1) := hc'pos (t + 1) (by omega)
    have hbn' : b ≤ c (t + 1) - c t := by omega
    have hg := hQ.geodesic t ht ht0 a b hab hbn'
    show wordDist D.alphabet.carrier
        (vertex v (normWord w lam 0 (c 1)
          (RelLetter.listVal ((w.drop 0).take (c 1 - 0)))) (c' t + a))
        (vertex v (normWord w lam 0 (c 1)
          (RelLetter.listVal ((w.drop 0).take (c 1 - 0)))) (c' t + b)) = b - a
    rw [show c' t + a = 1 + ((c t - c 1) + a) from by omega,
      show c' t + b = 1 + ((c t - c 1) + b) from by omega,
      hvadd ((c t - c 1) + a), hvadd ((c t - c 1) + b),
      show c 1 + ((c t - c 1) + a) = c t + a from by omega,
      show c 1 + ((c t - c 1) + b) = c t + b from by omega]
    exact hg
  · rw [hv0, hv1, hst]

/-! ## The ending shared by every single-connector branch -/

/-- **`short_cycle_of_indices` with the two constants of the base case fixed.**
`theta = 10 delta` is the thinness constant and `80 delta + 14` the target
length, so a branch has only to produce two indices and three numerical
facts. -/
theorem short_cycle_at (D : RelGenSet G Λ) (lam : Λ) (v : G)
    {w : List (RelLetter G Λ)} (hlet : ∀ a ∈ w, D.IsLetter a)
    (hcl : RelLetter.listVal w = 1) (hcomp : IsComp lam w 0 1)
    (hiso : IsIsolated D.fam lam v w 0) {δ m j : ℕ} (hmj : m ≤ j)
    (hjw : j ≤ w.length)
    (hd : wordDist D.alphabet.carrier (vertex v w m) (vertex v w j) ≤ 10 * δ)
    (hoff : 10 * δ + 2 ≤ wordDist D.alphabet.carrier v (vertex v w m) ∨
      10 * δ + 2 ≤ wordDist D.alphabet.carrier v (vertex v w j))
    (hN : m + 10 * δ + (w.length - j) ≤ 80 * δ + 14) :
    ∃ q : List (RelLetter G Λ),
      (∀ a ∈ q, D.IsLetter a) ∧ RelLetter.listVal q = 1 ∧
      q.length ≤ 80 * δ + 14 ∧ IsComp lam q 0 1 ∧ IsIsolated D.fam lam v q 0 ∧
      (vertex v q 0)⁻¹ * vertex v q 1 = (vertex v w 0)⁻¹ * vertex v w 1 :=
  short_cycle_of_indices D lam v hlet hcl hcomp hiso hmj hjw hd hoff hN

/-! ## The case tree, on a normalised 4-gon -/

/-- **Lemma 4.16 at `mu = 1`, `b = 0`, `n = 4`, for a 4-gon whose distinguished
side is already one letter.**  The four branches are described in the module
header; the worst is `80 delta + 14`. -/
theorem exists_short_isolating_cycle_of_unit (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) (lam : Λ) {v : G}
    {w : List (RelLetter G Λ)} {c : ℕ → ℕ} {δ : ℕ}
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ)
    (hQ : GeodesicFourGon D v w c) (hc1 : c 1 = 1)
    (hcomp : IsComp lam w 0 1) (hiso : IsIsolated D.fam lam v w 0) :
    ∃ q : List (RelLetter G Λ),
      (∀ a ∈ q, D.IsLetter a) ∧ RelLetter.listVal q = 1 ∧
      q.length ≤ 80 * δ + 14 ∧ IsComp lam q 0 1 ∧ IsIsolated D.fam lam v q 0 ∧
      (vertex v q 0)⁻¹ * vertex v q 1 = (vertex v w 0)⁻¹ * vertex v w 1 := by
  have hS := D.alphabet.symmetricGenerating
  have hst : c 0 = 0 := hQ.start
  have hfin : c 4 = w.length := hQ.finish
  have hm1 : c 1 ≤ c 2 := hQ.mono (by omega : (1 : ℕ) ≤ 2)
  have hm2 : c 2 ≤ c 3 := hQ.mono (by omega : (2 : ℕ) ≤ 3)
  have hm3 : c 3 ≤ c 4 := hQ.mono (by omega : (3 : ℕ) ≤ 4)
  have hlast : vertex v w (c 4) = v := hQ.vertex_last D
  have hcompc : IsComp lam w (c 0) (c 1) := by
    rw [hst, hc1]
    exact hcomp
  have hg1 : IsGeodesicChain D.alphabet.carrier (fun m => vertex v w (c 1 + m))
      (c 2 - c 1) := hQ.geodesic 1 (by omega) (by omega)
  have hg2 : IsGeodesicChain D.alphabet.carrier (fun m => vertex v w (c 2 + m))
      (c 3 - c 2) := hQ.geodesic 2 (by omega) (by omega)
  have hg3 : IsGeodesicChain D.alphabet.carrier (fun m => vertex v w (c 3 + m))
      (c 4 - c 3) := hQ.geodesic 3 (by omega) (by omega)
  -- the two ends of the distinguished side are one alphabet letter apart
  have hd01 : wordDist D.alphabet.carrier v (vertex v w (c 1)) ≤ 1 := by
    have h := wordDist_le_one_of_mem_fam D
      (span_mem_fam_of_isComp D v hQ.letters hcomp)
    rw [hc1]
    rwa [vertex_zero] at h
  have hcm1 : wordDist D.alphabet.carrier (vertex v w (c 1)) v
      = wordDist D.alphabet.carrier v (vertex v w (c 1)) :=
    wordDist_comm hS (vertex v w (c 1)) v
  -- distances along the three non-exempt sides
  have hs1 : ∀ x : ℕ, c 1 ≤ x → x ≤ c 2 →
      wordDist D.alphabet.carrier (vertex v w (c 1)) (vertex v w x)
        = x - c 1 := by
    intro x h1 h2
    have h := hg1 0 (x - c 1) (by omega) (by omega)
    beta_reduce at h
    rwa [Nat.add_zero, Nat.sub_zero,
      show c 1 + (x - c 1) = x from by omega] at h
  have hs2 : ∀ x y : ℕ, c 2 ≤ x → x ≤ y → y ≤ c 3 →
      wordDist D.alphabet.carrier (vertex v w x) (vertex v w y) = y - x := by
    intro x y h1 h2 h3
    have h := hg2 (x - c 2) (y - c 2) (by omega) (by omega)
    beta_reduce at h
    rwa [show c 2 + (x - c 2) = x from by omega,
      show c 2 + (y - c 2) = y from by omega,
      show y - c 2 - (x - c 2) = y - x from by omega] at h
  have hs3 : ∀ x : ℕ, c 3 ≤ x → x ≤ c 4 →
      wordDist D.alphabet.carrier (vertex v w x) v = c 4 - x := by
    intro x h1 h2
    have h := hg3 (x - c 3) (c 4 - c 3) (by omega) (by omega)
    beta_reduce at h
    rwa [show c 3 + (x - c 3) = x from by omega,
      show c 3 + (c 4 - c 3) = c 4 from by omega,
      show c 4 - c 3 - (x - c 3) = c 4 - x from by omega, hlast] at h
  rcases Nat.lt_or_ge (c 2 - c 1) (10 * δ + 3) with hL1 | hL1
  · rcases Nat.lt_or_ge (c 4 - c 3) (10 * δ + 3) with hL3 | hL3
    · -- **Both flanks short.**  The polygon is its own cycle.
      refine ⟨w, hQ.letters, hQ.closed, ?_, hcomp, hiso, rfl⟩
      have hle : w.length ≤ 4 * (10 * δ + 1) + 6 :=
        hQ.length_le_of_corners_close D hcompc (by omega) (by omega) (by omega)
      omega
    · -- **Side 3 long, side 1 short.**  Offset backwards along side 3.
      have hjr : c 3 ≤ c 4 - (10 * δ + 3) := by omega
      have hdj : wordDist D.alphabet.carrier (vertex v w (c 4 - (10 * δ + 3))) v
          = 10 * δ + 3 := by
        have h := hs3 (c 4 - (10 * δ + 3)) (by omega) (by omega)
        rwa [show c 4 - (c 4 - (10 * δ + 3)) = 10 * δ + 3 from by omega] at h
      have hdjv : wordDist D.alphabet.carrier v
          (vertex v w (c 4 - (10 * δ + 3))) = 10 * δ + 3 := by
        rw [wordDist_comm hS]
        exact hdj
      rcases hQ.exists_index_close_side_three D hδ
          (i := c 4 - (10 * δ + 3)) (by omega) (by omega) with
        ⟨p, hdp, hpr⟩ | ⟨q0, hq0, hdq0⟩
      · -- the near vertex is on side 1 or side 2
        have hpc3 : p ≤ c 3 := by
          rcases hpr with ⟨-, h2⟩ | ⟨-, h2⟩
          · omega
          · omega
        have hdpv : wordDist D.alphabet.carrier v (vertex v w p)
            ≤ 20 * δ + 3 := by
          have htri := wordDist_triangle hS v
            (vertex v w (c 4 - (10 * δ + 3))) (vertex v w p)
          omega
        have hpb : p ≤ 40 * δ + 9 := by
          rcases hpr with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · omega
          · have hdv2 : wordDist D.alphabet.carrier v (vertex v w (c 2))
                ≤ 10 * δ + 3 := by
              have hx := hs1 (c 2) (by omega) (by omega)
              have htri := wordDist_triangle hS v (vertex v w (c 1))
                (vertex v w (c 2))
              omega
            have hgap := hs2 (c 2) p (by omega) (by omega) (by omega)
            have htri := wordDist_triangle hS (vertex v w (c 2)) v
              (vertex v w p)
            have hcm := wordDist_comm hS v (vertex v w (c 2))
            omega
        refine short_cycle_at D lam v hQ.letters hQ.closed hcomp hiso
          (m := p) (j := c 4 - (10 * δ + 3)) (by omega) (by omega) ?_
          (Or.inr (by omega)) (by omega)
        rw [wordDist_comm hS]
        exact hdp
      · -- the near vertex would be on the exempt side: excluded by the offset
        exfalso
        have hb : wordDist D.alphabet.carrier v q0 +
            wordDist D.alphabet.carrier q0 (vertex v w (c 1))
            = wordDist D.alphabet.carrier v (vertex v w (c 1)) := hq0
        have hcm := wordDist_comm hS (vertex v w (c 4 - (10 * δ + 3))) q0
        have htri := wordDist_triangle hS v q0
          (vertex v w (c 4 - (10 * δ + 3)))
        omega
  · -- **Side 1 long.**  Offset forwards along side 1.
    have hmr : c 1 + (10 * δ + 3) ≤ c 2 := by omega
    have hdm : wordDist D.alphabet.carrier (vertex v w (c 1))
        (vertex v w (c 1 + (10 * δ + 3))) = 10 * δ + 3 := by
      have h := hs1 (c 1 + (10 * δ + 3)) (by omega) (by omega)
      rwa [show c 1 + (10 * δ + 3) - c 1 = 10 * δ + 3 from by omega] at h
    have htri1 := wordDist_triangle hS (vertex v w (c 1)) v
      (vertex v w (c 1 + (10 * δ + 3)))
    have htri2 := wordDist_triangle hS v (vertex v w (c 1))
      (vertex v w (c 1 + (10 * δ + 3)))
    have hoffm : 10 * δ + 2 ≤ wordDist D.alphabet.carrier v
        (vertex v w (c 1 + (10 * δ + 3))) := by omega
    have hupm : wordDist D.alphabet.carrier v
        (vertex v w (c 1 + (10 * δ + 3))) ≤ 10 * δ + 4 := by omega
    rcases hQ.exists_index_close_side_one D hδ
        (i := c 1 + (10 * δ + 3)) (by omega) (by omega) with
      ⟨p, hdp, hpr⟩ | ⟨q0, hq0, hdq0⟩
    · -- the near vertex is on side 2 or side 3
      have hpc2 : c 2 ≤ p := by
        rcases hpr with ⟨h1, -⟩ | ⟨h1, -⟩
        · omega
        · omega
      have hpc4 : p ≤ c 4 := by
        rcases hpr with ⟨-, h2⟩ | ⟨-, h2⟩
        · omega
        · omega
      have hdpv : wordDist D.alphabet.carrier v (vertex v w p)
          ≤ 20 * δ + 4 := by
        have htri := wordDist_triangle hS v
          (vertex v w (c 1 + (10 * δ + 3))) (vertex v w p)
        omega
      rcases Nat.lt_or_ge (c 4 - c 3) (10 * δ + 3) with hL3 | hL3
      · -- side 3 is short: the tail is bounded through it
        have htail : w.length - p ≤ 40 * δ + 8 := by
          rcases hpr with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · have hgap := hs2 p (c 3) (by omega) (by omega) (by omega)
            have hd3 := hs3 (c 3) (by omega) (by omega)
            have hcm3 := wordDist_comm hS (vertex v w (c 3)) v
            have htri := wordDist_triangle hS (vertex v w p) v
              (vertex v w (c 3))
            have hcmp := wordDist_comm hS v (vertex v w p)
            omega
          · omega
        exact short_cycle_at D lam v hQ.letters hQ.closed hcomp hiso
          (m := c 1 + (10 * δ + 3)) (j := p) (by omega) (by omega) hdp
          (Or.inl hoffm) (by omega)
      · -- side 3 is long as well
        rcases hpr with ⟨hp1, hp2⟩ | ⟨hp1, hp2⟩
        · -- the first near vertex is on side 2; take the second offset
          have hjr : c 3 ≤ c 4 - (10 * δ + 3) := by omega
          have hdj : wordDist D.alphabet.carrier
              (vertex v w (c 4 - (10 * δ + 3))) v = 10 * δ + 3 := by
            have h := hs3 (c 4 - (10 * δ + 3)) (by omega) (by omega)
            rwa [show c 4 - (c 4 - (10 * δ + 3)) = 10 * δ + 3
              from by omega] at h
          have hdjv : wordDist D.alphabet.carrier v
              (vertex v w (c 4 - (10 * δ + 3))) = 10 * δ + 3 := by
            rw [wordDist_comm hS]
            exact hdj
          rcases hQ.exists_index_close_side_three D hδ
              (i := c 4 - (10 * δ + 3)) (by omega) (by omega) with
            ⟨p', hdp', hpr'⟩ | ⟨q0, hq0, hdq0⟩
          · have hdp'v : wordDist D.alphabet.carrier v (vertex v w p')
                ≤ 20 * δ + 3 := by
              have htri := wordDist_triangle hS v
                (vertex v w (c 4 - (10 * δ + 3))) (vertex v w p')
              omega
            rcases hpr' with ⟨hq1, hq2⟩ | ⟨hq1, hq2⟩
            · -- the second near vertex is on side 1: one connector suffices
              have hpb : p' ≤ 20 * δ + 5 := by
                have hgap := hs1 p' (by omega) (by omega)
                have htri := wordDist_triangle hS (vertex v w (c 1)) v
                  (vertex v w p')
                omega
              refine short_cycle_at D lam v hQ.letters hQ.closed hcomp hiso
                (m := p') (j := c 4 - (10 * δ + 3)) (by omega) (by omega) ?_
                (Or.inr (by omega)) (by omega)
              rw [wordDist_comm hS]
              exact hdp'
            · -- both near vertices are on side 2: two connectors
              obtain ⟨r, hrlet, hrval, hrlen, hrcos⟩ :=
                exists_connector D lam v hdp (Or.inl hoffm)
              have hdp'' : wordDist D.alphabet.carrier (vertex v w p')
                  (vertex v w (c 4 - (10 * δ + 3))) ≤ 10 * δ := by
                rw [wordDist_comm hS]
                exact hdp'
              obtain ⟨r', hr'let, hr'val, hr'len, hr'cos⟩ :=
                exists_connector D lam v hdp'' (Or.inr (by omega))
              rcases Nat.lt_or_ge p' p with hint | hint
              · -- the two pairs interleave: the six-block splice
                have hgp : p - p' ≤ 40 * δ + 7 := by
                  have hd2 := hs2 p' p (by omega) (by omega) (by omega)
                  have htri := wordDist_triangle hS (vertex v w p') v
                    (vertex v w p)
                  have hcm' := wordDist_comm hS v (vertex v w p')
                  omega
                obtain ⟨q, hk1, hk2, hk3, hk4, hk5, hk6⟩ :=
                  cycle_of_reversed_splice D hsymm lam v hQ.letters hQ.closed
                    hcomp hiso (m := c 1 + (10 * δ + 3)) (j := p') (m' := p)
                    (j' := c 4 - (10 * δ + 3))
                    (by omega) (by omega) (by omega) (by omega) hrlet hrval
                    hrcos hr'let hr'val hr'cos
                exact ⟨q, hk1, hk2, by omega, hk4, hk5, hk6⟩
              · -- the two pairs do not interleave: splice twice
                have hgp : p' - p ≤ 40 * δ + 7 := by
                  have hd2 := hs2 p p' (by omega) (by omega) (by omega)
                  have htri := wordDist_triangle hS (vertex v w p) v
                    (vertex v w p')
                  have hcm' := wordDist_comm hS v (vertex v w p)
                  omega
                obtain ⟨q, hk1, hk2, hk3, hk4, hk5, hk6⟩ :=
                  cycle_of_two_connectors D lam v hQ.letters hQ.closed hcomp
                    hiso (m := c 1 + (10 * δ + 3)) (j₁ := p) (m₂ := p')
                    (j₂ := c 4 - (10 * δ + 3))
                    (by omega) (by omega) (by omega) (by omega) hrlet hrval
                    hrcos hr'let hr'val hr'cos
                exact ⟨q, hk1, hk2, by omega, hk4, hk5, hk6⟩
          · exfalso
            have hb : wordDist D.alphabet.carrier v q0 +
                wordDist D.alphabet.carrier q0 (vertex v w (c 1))
                = wordDist D.alphabet.carrier v (vertex v w (c 1)) := hq0
            have hcm := wordDist_comm hS
              (vertex v w (c 4 - (10 * δ + 3))) q0
            have htri := wordDist_triangle hS v q0
              (vertex v w (c 4 - (10 * δ + 3)))
            omega
        · -- the first near vertex is on side 3: one connector suffices
          have htail : w.length - p ≤ 20 * δ + 4 := by
            have hd3 := hs3 p (by omega) (by omega)
            have hcmp := wordDist_comm hS (vertex v w p) v
            omega
          exact short_cycle_at D lam v hQ.letters hQ.closed hcomp hiso
            (m := c 1 + (10 * δ + 3)) (j := p) (by omega) (by omega) hdp
            (Or.inl hoffm) (by omega)
    · -- the near vertex would be on the exempt side: excluded by the offset
      exfalso
      have hb : wordDist D.alphabet.carrier v q0 +
          wordDist D.alphabet.carrier q0 (vertex v w (c 1))
          = wordDist D.alphabet.carrier v (vertex v w (c 1)) := hq0
      have hcm := wordDist_comm hS (vertex v w (c 1 + (10 * δ + 3))) q0
      have htri := wordDist_triangle hS v q0
        (vertex v w (c 1 + (10 * δ + 3)))
      omega

/-! ## Lemma 4.16 -/

/-- **Dahmani--Guirardel--Osin, Lemma 4.16, at `mu = 1`, `b = 0`, `n = 4`.**

From a 4-gon carrying an isolated `H lam`-component as its distinguished (and
exempt) side, a closed admissible word of length at most `100 (delta + 1)` in
which the component --- now a single letter at index `0` --- is still isolated,
with the same span.

The run is collapsed first (`exists_unit_side_zero`), then the case tree of
`exists_short_isolating_cycle_of_unit` runs; its worst branch is `80 delta + 14`
and `80 delta + 14 <= 100 (delta + 1)`.  The basepoint is returned because the
collapse and the splices are stated at a named basepoint and a consumer should
not have to know it is unchanged. -/
theorem exists_short_isolating_cycle (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) (lam : Λ) {v : G}
    {w : List (RelLetter G Λ)} {c : ℕ → ℕ} {δ : ℕ}
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ)
    (hQ : GeodesicFourGon D v w c) (hcomp : IsComp lam w (c 0) (c 1))
    (hiso : IsIsolated D.fam lam v w (c 0)) :
    ∃ (u : G) (q : List (RelLetter G Λ)),
      (∀ a ∈ q, D.IsLetter a) ∧ RelLetter.listVal q = 1 ∧
      q.length ≤ 100 * (δ + 1) ∧ IsComp lam q 0 1 ∧ IsIsolated D.fam lam u q 0 ∧
      (vertex u q 0)⁻¹ * vertex u q 1
        = (vertex v w (c 0))⁻¹ * vertex v w (c 1) := by
  obtain ⟨w', c', hQ', hc'1, hcomp', hiso', hspan'⟩ :=
    hQ.exists_unit_side_zero D hcomp hiso
  obtain ⟨q, hq1, hq2, hq3, hq4, hq5, hq6⟩ :=
    exists_short_isolating_cycle_of_unit D hsymm lam hδ hQ' hc'1 hcomp' hiso'
  refine ⟨v, q, hq1, hq2, by omega, hq4, hq5, ?_⟩
  rw [hq6]
  exact hspan'

end OsinComponents
end GGT
end GroupApproximation
