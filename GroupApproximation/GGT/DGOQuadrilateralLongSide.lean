import GroupApproximation.GGT.DGOWindmillQuasiconvex

/-!
# A long side of a hyperbolic quadrilateral shadows another side

This is the four-sided instance of DGO Lemma 3.2 needed by the proof of
Theorem 4.42.  Four equally spaced samples on one side are each `6δ`-close to
one of the other three sides.  Two samples therefore choose the same side;
their witnesses are still separated after paying the two `6δ` errors.
-/

namespace GroupApproximation
namespace GGT
namespace Elementary

open GroupApproximation.HullGeometry
open GroupApproximation.DGOWindmill

universe v

variable {X : Type v} [PseudoMetricSpace X]

/-- **Four-sided DGO Lemma 3.2.**  If the side `A--D` has length greater than
`3(β+12δ)`, it contains two points at parameter distance at least `β` which
are `6δ`-close to two points, also at distance at least `β`, on one common
other side of the quadrilateral. -/
theorem exists_long_close_pair_on_other_quadrilateral_side
    {δ β : ℝ} (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ)
    (hgeo : IsGeodesicSpace X) (hβ : 0 < β)
    {A B C D : X} {fAD fAB fBC fCD : ℝ → X}
    (hAD : IsGeodesicSegment fAD 0 (dist A D)) (hAD0 : fAD 0 = A)
    (hAD1 : fAD (dist A D) = D)
    (hAB : IsGeodesicSegment fAB 0 (dist A B)) (hAB0 : fAB 0 = A)
    (hAB1 : fAB (dist A B) = B)
    (hBC : IsGeodesicSegment fBC 0 (dist B C)) (hBC0 : fBC 0 = B)
    (hBC1 : fBC (dist B C) = C)
    (hCD : IsGeodesicSegment fCD 0 (dist C D)) (hCD0 : fCD 0 = C)
    (hCD1 : fCD (dist C D) = D)
    (hlong : 3 * (β + 12 * δ) < dist A D) :
    ∃ (j : Fin 3) (u u' s s' : ℝ),
      u ∈ Set.Icc (0 : ℝ) (dist A D) ∧
      u' ∈ Set.Icc (0 : ℝ) (dist A D) ∧ β ≤ u' - u ∧
      s ∈ Set.Icc (0 : ℝ)
        (![dist A B, dist B C, dist C D] j) ∧
      s' ∈ Set.Icc (0 : ℝ)
        (![dist A B, dist B C, dist C D] j) ∧
      β ≤ |s' - s| ∧
      dist (fAD u) (![fAB, fBC, fCD] j s) ≤ 6 * δ ∧
      dist (fAD u') (![fAB, fBC, fCD] j s') ≤ 6 * δ := by
  classical
  let Δ : ℝ := β + 12 * δ
  let sideLength : Fin 3 → ℝ := ![dist A B, dist B C, dist C D]
  let side : Fin 3 → ℝ → X := ![fAB, fBC, fCD]
  let sample : Fin 4 → ℝ := fun i ↦ (i : ℝ) * Δ
  have hΔ0 : 0 < Δ := by dsimp [Δ]; linarith
  have hsample (i : Fin 4) : sample i ∈ Set.Icc (0 : ℝ) (dist A D) := by
    have hi : (i : ℕ) ≤ 3 := by omega
    have hiR : (i : ℝ) ≤ 3 := by exact_mod_cast hi
    constructor
    · dsimp [sample]
      positivity
    · dsimp [sample]
      nlinarith
  have hall : ∀ i : Fin 4, ∃ j : Fin 3, ∃ s : ℝ,
      s ∈ Set.Icc (0 : ℝ) (sideLength j) ∧
        dist (fAD (sample i)) (side j s) ≤ 6 * δ := by
    intro i
    rcases exists_close_on_other_sides_of_quadrilateral hδ hδ0 hgeo
        hAD hAD0 hAD1 hAB hAB0 hAB1 hBC hBC0 hBC1 hCD hCD0 hCD1
        (hsample i) with h | h | h
    · obtain ⟨s, hs, hd⟩ := h
      exact ⟨0, s, by simpa [sideLength], by simpa [side]⟩
    · obtain ⟨s, hs, hd⟩ := h
      exact ⟨1, s, by simpa [sideLength], by simpa [side]⟩
    · obtain ⟨s, hs, hd⟩ := h
      exact ⟨2, s, by simpa [sideLength], by simpa [side]⟩
  choose owner witness hwitness hclose using hall
  have hcard : Fintype.card (Fin 3) < Fintype.card (Fin 4) := by decide
  obtain ⟨i, k, hik, howner⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt owner hcard
  have hfinish : ∀ (i k : Fin 4), (i : ℕ) < k → owner i = owner k →
      ∃ (j : Fin 3) (u u' s s' : ℝ),
        u ∈ Set.Icc (0 : ℝ) (dist A D) ∧
        u' ∈ Set.Icc (0 : ℝ) (dist A D) ∧ β ≤ u' - u ∧
        s ∈ Set.Icc (0 : ℝ) (sideLength j) ∧
        s' ∈ Set.Icc (0 : ℝ) (sideLength j) ∧
        β ≤ |s' - s| ∧
        dist (fAD u) (side j s) ≤ 6 * δ ∧
        dist (fAD u') (side j s') ≤ 6 * δ := by
    intro i k hik hown
    have hstepNat : (i : ℕ) + 1 ≤ k := by omega
    have hstep : (i : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hstepNat
    have huspan : β ≤ sample k - sample i := by
      dsimp [sample, Δ]
      nlinarith
    have hside : IsGeodesicSegment (side (owner i)) 0
        (sideLength (owner i)) := by
      have hj : owner i = 0 ∨ owner i = 1 ∨ owner i = 2 := by omega
      rcases hj with hj | hj | hj
      · rw [hj]
        simpa [side, sideLength] using hAB
      · rw [hj]
        simpa [side, sideLength] using hBC
      · rw [hj]
        simpa [side, sideLength] using hCD
    have hsi : witness i ∈ Set.Icc (0 : ℝ) (sideLength (owner i)) :=
      hwitness i
    have hsk : witness k ∈ Set.Icc (0 : ℝ) (sideLength (owner i)) := by
      rw [hown]
      exact hwitness k
    have hmain : dist (fAD (sample i)) (fAD (sample k)) = sample k - sample i := by
      rw [hAD (sample i) (hsample i) (sample k) (hsample k)]
      rw [abs_of_nonpos]
      · ring
      · exact sub_nonpos.mpr (by linarith [huspan, hβ])
    have hshadow : dist (side (owner i) (witness i))
        (side (owner i) (witness k)) = |witness i - witness k| :=
      hside _ hsi _ hsk
    have hclosek : dist (fAD (sample k))
        (side (owner i) (witness k)) ≤ 6 * δ := by
      rw [hown]
      exact hclose k
    have hclosek' : dist (side (owner i) (witness k))
        (fAD (sample k)) ≤ 6 * δ := by
      rwa [dist_comm]
    have hsep : β ≤ |witness k - witness i| := by
      have htri := dist_triangle4 (fAD (sample i))
        (side (owner i) (witness i))
        (side (owner i) (witness k)) (fAD (sample k))
      rw [hmain, hshadow, abs_sub_comm] at htri
      have hclosei := hclose i
      nlinarith [hclosek']
    refine ⟨owner i, sample i, sample k, witness i, witness k,
      hsample i, hsample k, huspan, hsi, hsk, hsep, hclose i, hclosek⟩
  have hvalne : (i : ℕ) ≠ k := Fin.val_ne_of_ne hik
  rcases lt_or_gt_of_ne hvalne with hlt | hgt
  · simpa [side, sideLength] using hfinish i k hlt howner
  · simpa [side, sideLength, abs_sub_comm] using hfinish k i hgt howner.symm

end Elementary
end GGT
end GroupApproximation
