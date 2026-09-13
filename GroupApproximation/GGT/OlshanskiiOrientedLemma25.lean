import GroupApproximation.GGT.OlshanskiiFirstVisit
import GroupApproximation.Meta.AxiomGuard

/-!
# Ol'shanskii's Lemma 25 with antiparallel segments

`exists_long_close_pair` (`OlshanskiiLemma25`) finds a long side `b` of a closed
geodesic `n`-gon and another side `i` of the class `S`, together with two pairs
of `D`-close points that are `β` apart on both sides. It leaves the relative
direction of the two segments open: its conclusion is `β ≤ |s' - s|`.

This module proves the oriented statement. Assume `n ≤ 2 ^ c` in place of
`n - 1 ≤ 2 ^ c`. Then the two segments are antiparallel: as the parameter on
side `b` increases from `u` to `u'`, the close points on side `i` decrease from
`s'` to `s`. The loop `b, b + 1, …, b + n - 1` reads both sides forwards, so it
reads the two segments in opposite directions. This is the configuration in
which the region between the segments has boundary `q₁ s₁ q₂⁻¹ s₂`, which the
planar Case 1 of Osin's Lemma 9.4 (math/0411039v3) uses.

The proof is the sampling argument of `exists_long_close_pair`, except that each
sample records its first-visit witness (`exists_firstVisit_witnesses`) rather
than an arbitrary one. Samples are `β + 2D > 6δ(c+1)` apart. By
`exists_close_prefix_side`, two samples `p < q` recording the same side have
witness parameters `sf p ≤ sf q`, so the estimate `β ≤ |sf q - sf p|` becomes
`β ≤ sf q - sf p`. The sample `σ p` reads side `b` backwards, so it is the
parameter `L - σ p` read forwards, and the larger `u` pairs with the smaller
`s`. The counting half of the argument is unchanged.
-/

namespace GroupApproximation
namespace Olshanskii

open GroupApproximation.HullGeometry

universe v

variable {X : Type v} [PseudoMetricSpace X]

/-- **Ol'shanskii's Lemma 25, antiparallel form.** Take a closed geodesic
`n`-gon read from `b`, with `n ≤ 2 ^ c`. Split the sides other than `b` into a
class `S` and its complement, and bound the length of each side outside `S` by
`w i`, with `∑ w ≤ ρ`. If side `b` is longer than `(n-1)(β + 4D) + ρ`, then some
side `i` in `S` carries parameters `s < s'` and side `b` carries parameters
`u < u'`, each pair at least `β` apart, with `sides b u` within `D` of
`sides i s'` and `sides b u'` within `D` of `sides i s`. -/
theorem exists_long_antiparallel_pair {δ D ρ β : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ) (hgeo : IsGeodesicSpace X)
    {n c b : ℕ} (hn : 2 ≤ n) (hc : n ≤ 2 ^ c)
    {vs : ℕ → X} {sides : ℕ → ℝ → X}
    (hpoly : IsClosedPolygonAt vs sides b n)
    (hD : 3 * δ * ((c : ℝ) + 1) ≤ D)
    (S : Set ℕ) (w : ℕ → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hshort : ∀ i, b < i → i < b + n → i ∉ S → dist (vs i) (vs (i + 1)) ≤ w i)
    (hρ : ∑ j ∈ Finset.range (n - 1), w (b + 1 + j) ≤ ρ)
    (hβ : 0 < β)
    (hlong : ((n : ℝ) - 1) * (β + 4 * D) + ρ < dist (vs b) (vs (b + 1))) :
    ∃ i, b < i ∧ i < b + n ∧ i ∈ S ∧
      ∃ u ∈ Set.Icc (0 : ℝ) (dist (vs b) (vs (b + 1))),
        ∃ u' ∈ Set.Icc (0 : ℝ) (dist (vs b) (vs (b + 1))),
          ∃ s ∈ Set.Icc (0 : ℝ) (dist (vs i) (vs (i + 1))),
            ∃ s' ∈ Set.Icc (0 : ℝ) (dist (vs i) (vs (i + 1))),
              β ≤ u' - u ∧ β ≤ s' - s ∧
                dist (sides b u) (sides i s') ≤ D ∧
                dist (sides b u') (sides i s) ≤ D := by
  have hside := hpoly.1
  have hbn : b < b + n := by omega
  obtain ⟨hb, -, -⟩ := hside b (le_refl b) hbn
  have hLnn : (0 : ℝ) ≤ dist (vs b) (vs (b + 1)) := dist_nonneg
  have hcast0 : (0 : ℝ) ≤ (c : ℝ) := Nat.cast_nonneg c
  have hD0 : (0 : ℝ) ≤ 3 * δ * ((c : ℝ) + 1) :=
    mul_nonneg (by linarith) (by linarith)
  have hDnn : (0 : ℝ) ≤ D := le_trans hD0 hD
  have hstep : (0 : ℝ) < β + 2 * D := by linarith
  -- the samples along side `b`, clamped to its length
  obtain ⟨σ, hσ⟩ : ∃ σ : ℕ → ℝ, ∀ k : ℕ,
      σ k = min ((k : ℝ) * (β + 2 * D)) (dist (vs b) (vs (b + 1))) :=
    ⟨fun k => min ((k : ℝ) * (β + 2 * D)) (dist (vs b) (vs (b + 1))),
      fun _ => rfl⟩
  have hσmem : ∀ k, σ k ∈ Set.Icc (0 : ℝ) (dist (vs b) (vs (b + 1))) := by
    intro k
    rw [hσ k]
    refine ⟨?_, min_le_right _ _⟩
    have h1 : (0 : ℝ) ≤ (k : ℝ) * (β + 2 * D) :=
      mul_nonneg (Nat.cast_nonneg k) hstep.le
    exact le_min h1 hLnn
  -- each sample records its first-visit witness
  obtain ⟨jt, st, hwit⟩ := exists_firstVisit_witnesses hδ hδ0 hgeo hn
    (le_trans (Nat.sub_le n 1) hc) hpoly
  obtain ⟨jf, hjf'⟩ : ∃ jf : ℕ → ℕ, ∀ k, jf k = jt (σ k) :=
    ⟨fun k => jt (σ k), fun _ => rfl⟩
  obtain ⟨sf, hsf'⟩ : ∃ sf : ℕ → ℝ, ∀ k, sf k = st (σ k) :=
    ⟨fun k => st (σ k), fun _ => rfl⟩
  have hjf : ∀ k, jf k < n - 1 := by
    intro k
    rw [hjf' k]
    exact (hwit (σ k) (hσmem k)).1
  have hsf : ∀ k, sf k ∈ Set.Icc (0 : ℝ)
      (dist (vs (b + 1 + jf k)) (vs (b + 1 + jf k + 1))) := by
    intro k
    rw [hjf' k, hsf' k]
    exact (hwit (σ k) (hσmem k)).2.1
  have hdf : ∀ k, dist (sides b (dist (vs b) (vs (b + 1)) - σ k))
      (sides (b + 1 + jf k) (sf k)) ≤ 3 * δ * ((c : ℝ) + 1) := by
    intro k
    rw [hjf' k, hsf' k]
    exact (hwit (σ k) (hσmem k)).2.2.1
  -- two samples recording the same side are close along it
  have hcore : ∀ k k' : ℕ, jf k = jf k' →
      |σ k - σ k'| ≤ 2 * (3 * δ * ((c : ℝ) + 1)) + |sf k - sf k'| := by
    intro k k' heq
    have h1 : b ≤ b + 1 + jf k := by omega
    have h2 : b + 1 + jf k < b + n := by
      have hjk := hjf k
      omega
    obtain ⟨hgj, -, -⟩ := hside (b + 1 + jf k) h1 h2
    have hsk : sf k ∈ Set.Icc (0 : ℝ)
        (dist (vs (b + 1 + jf k)) (vs (b + 1 + jf k + 1))) := hsf k
    have hsk' : sf k' ∈ Set.Icc (0 : ℝ)
        (dist (vs (b + 1 + jf k)) (vs (b + 1 + jf k + 1))) := by
      rw [heq]
      exact hsf k'
    have hdk : dist (sides b (dist (vs b) (vs (b + 1)) - σ k))
        (sides (b + 1 + jf k) (sf k)) ≤ 3 * δ * ((c : ℝ) + 1) := hdf k
    have hdk' : dist (sides b (dist (vs b) (vs (b + 1)) - σ k'))
        (sides (b + 1 + jf k) (sf k')) ≤ 3 * δ * ((c : ℝ) + 1) := by
      rw [heq]
      exact hdf k'
    have hmk := hσmem k
    have hmk' := hσmem k'
    have hxk : dist (vs b) (vs (b + 1)) - σ k
        ∈ Set.Icc (0 : ℝ) (dist (vs b) (vs (b + 1))) :=
      ⟨by linarith [hmk.2], by linarith [hmk.1]⟩
    have hxk' : dist (vs b) (vs (b + 1)) - σ k'
        ∈ Set.Icc (0 : ℝ) (dist (vs b) (vs (b + 1))) :=
      ⟨by linarith [hmk'.2], by linarith [hmk'.1]⟩
    have hspan : dist (sides b (dist (vs b) (vs (b + 1)) - σ k))
        (sides b (dist (vs b) (vs (b + 1)) - σ k')) = |σ k - σ k'| := by
      rw [hb _ hxk _ hxk']
      have he : dist (vs b) (vs (b + 1)) - σ k
          - (dist (vs b) (vs (b + 1)) - σ k') = -(σ k - σ k') := by ring
      rw [he, abs_neg]
    have hwit' : dist (sides (b + 1 + jf k) (sf k))
        (sides (b + 1 + jf k) (sf k')) = |sf k - sf k'| := hgj _ hsk _ hsk'
    have h4 := dist_triangle4 (sides b (dist (vs b) (vs (b + 1)) - σ k))
      (sides (b + 1 + jf k) (sf k)) (sides (b + 1 + jf k) (sf k'))
      (sides b (dist (vs b) (vs (b + 1)) - σ k'))
    have hsym : dist (sides (b + 1 + jf k) (sf k'))
        (sides b (dist (vs b) (vs (b + 1)) - σ k'))
        = dist (sides b (dist (vs b) (vs (b + 1)) - σ k'))
          (sides (b + 1 + jf k) (sf k')) := dist_comm _ _
    rw [hspan, hwit', hsym] at h4
    linarith
  -- how many samples fit along side `b`
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ,
      N = ⌊dist (vs b) (vs (b + 1)) / (β + 2 * D)⌋₊ :=
    ⟨⌊dist (vs b) (vs (b + 1)) / (β + 2 * D)⌋₊, rfl⟩
  have hNle : (N : ℝ) * (β + 2 * D) ≤ dist (vs b) (vs (b + 1)) := by
    rw [hNdef]
    have h1 : ((⌊dist (vs b) (vs (b + 1)) / (β + 2 * D)⌋₊ : ℕ) : ℝ)
        ≤ dist (vs b) (vs (b + 1)) / (β + 2 * D) :=
      Nat.floor_le (div_nonneg hLnn hstep.le)
    exact (le_div_iff₀ hstep).mp h1
  have hNgt : dist (vs b) (vs (b + 1)) < ((N : ℝ) + 1) * (β + 2 * D) := by
    rw [hNdef]
    have h1 : dist (vs b) (vs (b + 1)) / (β + 2 * D)
        < (⌊dist (vs b) (vs (b + 1)) / (β + 2 * D)⌋₊ : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    exact (div_lt_iff₀ hstep).mp h1
  have hσeq : ∀ k : ℕ, k ≤ N → σ k = (k : ℝ) * (β + 2 * D) := by
    intro k hk
    rw [hσ k]
    refine min_eq_left ?_
    have hkc : (k : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr hk
    have hmul := mul_le_mul_of_nonneg_right hkc hstep.le
    linarith
  -- the fibres of the recorded index
  obtain ⟨F, hF⟩ : ∃ F : ℕ → Finset ℕ, ∀ j : ℕ,
      F j = (Finset.range (N + 1)).filter (fun k => jf k = j) :=
    ⟨fun j => (Finset.range (N + 1)).filter (fun k => jf k = j), fun _ => rfl⟩
  by_contra hcon
  -- no side of `S` records two samples, or the conclusion would hold
  have hfiberS : ∀ j : ℕ, j < n - 1 → b + 1 + j ∈ S → (F j).card ≤ 1 := by
    intro j hj hjS
    have hwin : ∀ p q : ℕ, p ≤ N → q ≤ N → p < q → jf p = j → jf q = j →
        False := by
      intro p q hpN hqN hpq hjp hjq
      apply hcon
      have hlt1 : b < b + 1 + j := by omega
      have hlt2 : b + 1 + j < b + n := by omega
      have hσp : σ p = (p : ℝ) * (β + 2 * D) := hσeq p hpN
      have hσq : σ q = (q : ℝ) * (β + 2 * D) := hσeq q hqN
      have hpqN : p + 1 ≤ q := by omega
      have hpqR : (p : ℝ) + 1 ≤ (q : ℝ) := by exact_mod_cast hpqN
      have hgap : β + 2 * D ≤ σ q - σ p := by
        have h1 : ((p : ℝ) + 1) * (β + 2 * D) ≤ (q : ℝ) * (β + 2 * D) :=
          mul_le_mul_of_nonneg_right hpqR hstep.le
        rw [hσp, hσq]
        linarith
      have hnn : (0 : ℝ) ≤ σ q - σ p := by linarith
      have hcc := hcore p q (hjp.trans hjq.symm)
      have habs : |σ p - σ q| = σ q - σ p := by
        rw [abs_sub_comm]
        exact abs_of_nonneg hnn
      rw [habs] at hcc
      have hsfgap : β ≤ |sf p - sf q| := by linarith
      -- first-visit witnesses are monotone along side `b`
      have hmono : sf p ≤ sf q := by
        obtain ⟨j0, hj0, s0, hs0, hd0, hlex⟩ := exists_close_prefix_side hδ hδ0 hgeo hc
          hpoly (hσmem p).1 (hσmem q).2 (by linarith) (hjf q) (hsf q) (hdf q)
        have hmin := (hwit (σ p) (hσmem p)).2.2.2 j0 hj0 s0 hs0 hd0
        rw [← hjf' p, ← hsf' p] at hmin
        rcases hmin with hlt' | ⟨heq', hle'⟩
        · exfalso
          rcases hlex with hlt | ⟨heq, -⟩ <;> omega
        · rcases hlex with hlt | ⟨-, hle⟩
          · exfalso
            omega
          · linarith
      have hsfgap' : β ≤ sf q - sf p := by
        have h1 : |sf p - sf q| = sf q - sf p := by
          rw [abs_sub_comm]
          exact abs_of_nonneg (by linarith)
        linarith
      have hmp := hσmem p
      have hmq := hσmem q
      have hup : dist (vs b) (vs (b + 1)) - σ q
          ∈ Set.Icc (0 : ℝ) (dist (vs b) (vs (b + 1))) :=
        ⟨by linarith [hmq.2], by linarith [hmq.1]⟩
      have huq : dist (vs b) (vs (b + 1)) - σ p
          ∈ Set.Icc (0 : ℝ) (dist (vs b) (vs (b + 1))) :=
        ⟨by linarith [hmp.2], by linarith [hmp.1]⟩
      have hsq : sf q ∈ Set.Icc (0 : ℝ)
          (dist (vs (b + 1 + j)) (vs (b + 1 + j + 1))) := by
        have h := hsf q
        rw [hjq] at h
        exact h
      have hsp : sf p ∈ Set.Icc (0 : ℝ)
          (dist (vs (b + 1 + j)) (vs (b + 1 + j + 1))) := by
        have h := hsf p
        rw [hjp] at h
        exact h
      have hdq : dist (sides b (dist (vs b) (vs (b + 1)) - σ q))
          (sides (b + 1 + j) (sf q)) ≤ D := by
        have h := hdf q
        rw [hjq] at h
        linarith
      have hdp : dist (sides b (dist (vs b) (vs (b + 1)) - σ p))
          (sides (b + 1 + j) (sf p)) ≤ D := by
        have h := hdf p
        rw [hjp] at h
        linarith
      have hspangoal : β ≤ dist (vs b) (vs (b + 1)) - σ p
          - (dist (vs b) (vs (b + 1)) - σ q) := by linarith
      exact ⟨b + 1 + j, hlt1, hlt2, hjS,
        dist (vs b) (vs (b + 1)) - σ q, hup,
        dist (vs b) (vs (b + 1)) - σ p, huq,
        sf p, hsp, sf q, hsq, hspangoal, hsfgap', hdq, hdp⟩
    by_contra hc2
    have hc3 : 1 < (F j).card := by omega
    obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp hc3
    rw [hF j] at hp hq
    have hpm := Finset.mem_filter.mp hp
    have hqm := Finset.mem_filter.mp hq
    have hpr := Finset.mem_range.mp hpm.1
    have hqr := Finset.mem_range.mp hqm.1
    have hpN : p ≤ N := by omega
    have hqN : q ≤ N := by omega
    rcases lt_or_gt_of_ne hpq with hlt | hlt
    · exact hwin p q hpN hqN hlt hpm.2 hqm.2
    · exact hwin q p hqN hpN hlt hqm.2 hpm.2
  -- every fibre is short: the `S`-sides by the above, the others by `w`
  have hfiber : ∀ j : ℕ, j < n - 1 →
      ((F j).card : ℝ) * (β + 2 * D)
        ≤ (β + 2 * D) + w (b + 1 + j) + 2 * D := by
    intro j hj
    have hwj := hw (b + 1 + j)
    rcases Classical.em (b + 1 + j ∈ S) with hjS | hjS
    · have h1 := hfiberS j hj hjS
      have h2 : ((F j).card : ℝ) ≤ 1 := by exact_mod_cast h1
      have h3 : ((F j).card : ℝ) * (β + 2 * D) ≤ 1 * (β + 2 * D) :=
        mul_le_mul_of_nonneg_right h2 hstep.le
      linarith
    · have hlt1 : b < b + 1 + j := by omega
      have hlt2 : b + 1 + j < b + n := by omega
      have hshortj : dist (vs (b + 1 + j)) (vs (b + 1 + j + 1))
          ≤ w (b + 1 + j) := hshort (b + 1 + j) hlt1 hlt2 hjS
      rcases Finset.eq_empty_or_nonempty (F j) with he | hne
      · rw [he]
        simp only [Finset.card_empty, Nat.cast_zero, zero_mul]
        linarith
      · have hmemfil : ∀ k, k ∈ F j → k ∈ Finset.range (N + 1) ∧ jf k = j := by
          intro k hk
          rw [hF j] at hk
          exact Finset.mem_filter.mp hk
        have hminmem : (F j).min' hne ∈ F j := Finset.min'_mem _ _
        have hmaxmem : (F j).max' hne ∈ F j := Finset.max'_mem _ _
        have hminle : (F j).min' hne ≤ (F j).max' hne :=
          Finset.min'_le (F j) _ hmaxmem
        have hsub : F j ⊆ Finset.Icc ((F j).min' hne) ((F j).max' hne) := by
          intro k hk
          rw [Finset.mem_Icc]
          exact ⟨Finset.min'_le (F j) k hk, Finset.le_max' (F j) k hk⟩
        have hcard : (F j).card ≤ (F j).max' hne + 1 - (F j).min' hne := by
          have h1 := Finset.card_le_card hsub
          rwa [Nat.card_Icc] at h1
        have hminfil := hmemfil _ hminmem
        have hmaxfil := hmemfil _ hmaxmem
        have hminr := Finset.mem_range.mp hminfil.1
        have hmaxr := Finset.mem_range.mp hmaxfil.1
        have hminN : (F j).min' hne ≤ N := by omega
        have hmaxN : (F j).max' hne ≤ N := by omega
        have hjmin : jf ((F j).min' hne) = j := hminfil.2
        have hjmax : jf ((F j).max' hne) = j := hmaxfil.2
        have hσmin := hσeq _ hminN
        have hσmax := hσeq _ hmaxN
        have h1 : sf ((F j).min' hne) ∈ Set.Icc (0 : ℝ)
            (dist (vs (b + 1 + j)) (vs (b + 1 + j + 1))) := by
          have h := hsf ((F j).min' hne)
          rw [hjmin] at h
          exact h
        have h2 : sf ((F j).max' hne) ∈ Set.Icc (0 : ℝ)
            (dist (vs (b + 1 + j)) (vs (b + 1 + j + 1))) := by
          have h := hsf ((F j).max' hne)
          rw [hjmax] at h
          exact h
        have hsfle : |sf ((F j).min' hne) - sf ((F j).max' hne)|
            ≤ dist (vs (b + 1 + j)) (vs (b + 1 + j + 1)) := by
          refine abs_le.mpr ⟨?_, ?_⟩
          · linarith [h1.1, h1.2, h2.1, h2.2]
          · linarith [h1.1, h1.2, h2.1, h2.2]
        have hcc := hcore ((F j).min' hne) ((F j).max' hne)
          (hjmin.trans hjmax.symm)
        have hcastle : (((F j).min' hne : ℕ) : ℝ)
            ≤ (((F j).max' hne : ℕ) : ℝ) := Nat.cast_le.mpr hminle
        have hmulle : (((F j).min' hne : ℕ) : ℝ) * (β + 2 * D)
            ≤ (((F j).max' hne : ℕ) : ℝ) * (β + 2 * D) :=
          mul_le_mul_of_nonneg_right hcastle hstep.le
        have habs : |σ ((F j).min' hne) - σ ((F j).max' hne)|
            = σ ((F j).max' hne) - σ ((F j).min' hne) := by
          rw [abs_sub_comm]
          refine abs_of_nonneg ?_
          rw [hσmin, hσmax]
          linarith
        rw [habs, hσmin, hσmax] at hcc
        have hle1 : (F j).min' hne ≤ (F j).max' hne + 1 := by omega
        have hcast : (((F j).max' hne + 1 - (F j).min' hne : ℕ) : ℝ)
            = (((F j).max' hne : ℕ) : ℝ) + 1
              - (((F j).min' hne : ℕ) : ℝ) := by
          rw [Nat.cast_sub hle1, Nat.cast_add, Nat.cast_one]
        have hcard1 : ((F j).card : ℝ)
            ≤ (((F j).max' hne + 1 - (F j).min' hne : ℕ) : ℝ) :=
          Nat.cast_le.mpr hcard
        rw [hcast] at hcard1
        have hmul : ((F j).card : ℝ) * (β + 2 * D)
            ≤ ((((F j).max' hne : ℕ) : ℝ) + 1
              - (((F j).min' hne : ℕ) : ℝ)) * (β + 2 * D) :=
          mul_le_mul_of_nonneg_right hcard1 hstep.le
        linarith
  -- the fibrewise count
  have hcount : N + 1 = ∑ j ∈ Finset.range (n - 1), (F j).card := by
    have hmaps : ∀ k ∈ Finset.range (N + 1), jf k ∈ Finset.range (n - 1) := by
      intro k _
      exact Finset.mem_range.mpr (hjf k)
    have h1 := Finset.card_eq_sum_card_fiberwise hmaps
    rw [Finset.card_range] at h1
    rw [h1]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [hF j]
  have hNR : (N : ℝ) + 1
      = ∑ j ∈ Finset.range (n - 1), (((F j).card : ℕ) : ℝ) := by
    have h2 : ((N + 1 : ℕ) : ℝ)
        = ((∑ j ∈ Finset.range (n - 1), (F j).card : ℕ) : ℝ) := by
      rw [hcount]
    push_cast at h2
    exact h2
  have h1n : 1 ≤ n := by omega
  have hcastn : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub h1n, Nat.cast_one]
  have hsum : ((N : ℝ) + 1) * (β + 2 * D)
      ≤ ((n : ℝ) - 1) * (β + 4 * D) + ρ := by
    calc ((N : ℝ) + 1) * (β + 2 * D)
        = (∑ j ∈ Finset.range (n - 1), (((F j).card : ℕ) : ℝ))
            * (β + 2 * D) := by rw [hNR]
      _ = ∑ j ∈ Finset.range (n - 1), (((F j).card : ℕ) : ℝ) * (β + 2 * D) := by
          rw [Finset.sum_mul]
      _ ≤ ∑ j ∈ Finset.range (n - 1), ((β + 4 * D) + w (b + 1 + j)) := by
          refine Finset.sum_le_sum ?_
          intro j hj
          have hfj := hfiber j (Finset.mem_range.mp hj)
          linarith
      _ = (∑ _j ∈ Finset.range (n - 1), (β + 4 * D))
            + ∑ j ∈ Finset.range (n - 1), w (b + 1 + j) := Finset.sum_add_distrib
      _ = ((n : ℝ) - 1) * (β + 4 * D)
            + ∑ j ∈ Finset.range (n - 1), w (b + 1 + j) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hcastn]
      _ ≤ ((n : ℝ) - 1) * (β + 4 * D) + ρ := by linarith
  linarith

#audit_axioms GroupApproximation.Olshanskii.exists_long_antiparallel_pair

end Olshanskii
end GroupApproximation
