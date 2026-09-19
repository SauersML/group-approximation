import GroupApproximation.GGT.DGOAssemblySubdivision

/-!
# Balanced cuts for general quasi-geodesic polygons

The Morse lower-progress constant is `1 / mu`. The additive chord constant
is chosen before the polygon and depends only on its genuine quasi-geodesic
parameters and the hyperbolicity constant. No bound on side lengths is used.
-/

namespace GroupApproximation.GGT.DGOPolygonCut

open GroupApproximation.GGT.OsinComponents
open GroupApproximation.WordMetric
open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w
variable {G : Type u} [Group G] {Lambda : Type w}

/-- Quarter-separated original sides contain vertices joined by a uniformly
logarithmic-length chord, at arbitrary positive multiplicative parameter. -/
theorem exists_balanced_interior_cut_word_quasi (D : RelGenSet G Lambda)
    (mu b : ℝ) (hmu : 0 < mu) (hb : 0 ≤ b) {delta : ℕ}
    (hdelta : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) :
    ∃ R : ℕ, ∀ {n k : ℕ}, 8 ≤ n → n ≤ 2 ^ k → ∀ (v : G)
      (word : List (RelLetter G Lambda)) (cut : ℕ → ℕ),
      (∀ a ∈ word, D.IsLetter a) → RelLetter.listVal word = 1 →
      IsPolygonCut n word cut →
      (∀ s : ℕ, s < n → ∀ p q : ℕ,
        cut s ≤ p → p ≤ q → q ≤ cut (s + 1) →
        ((q - p : ℕ) : ℝ) / mu - b ≤
          ((wordDist D.alphabet.carrier (vertex v word p)
            (vertex v word q) : ℕ) : ℝ)) →
      ∃ a b' i j : ℕ, a < b' ∧ b' < n ∧
        n ≤ 4 * (b' - a) ∧ 4 * (b' - a) ≤ 3 * n ∧
        cut a ≤ i ∧ i ≤ cut (a + 1) ∧
        cut b' ≤ j ∧ j ≤ cut (b' + 1) ∧
        wordDist D.alphabet.carrier (vertex v word i) (vertex v word j)
          ≤ 6 * (delta + 6) * (k + 1) + R := by
  have hdelta0 : (0 : ℝ) ≤ (delta : ℝ) + 6 := by positivity
  obtain ⟨K, hK0, hK⟩ :=
    ElementaryMorse.exists_bound_chord_near_chain_uniform
      (δ := (delta : ℝ) + 6) (D := 2) (l := 1 / mu) (B := b + 1)
      hdelta0 (by positivity) (by positivity) (by positivity)
  refine ⟨⌈2 * K + 2⌉₊, ?_⟩
  intro n k hn hk v word cut hletters hclosed hcut hquasi
  let W := CayleyGeodesicModel.PointQuot D.alphabet
  let points : ℕ → W := fun s => iotaG D.alphabet (cutVertex v word cut s)
  have hgeo : IsGeodesicSpace W :=
    CayleyGeodesicModel.isGeodesicRealisationQuot D.alphabet
  have hhypC : IsHyperbolicSpace ((delta : ℝ)) (Cayley D.alphabet) :=
    isHyperbolicSpace_cayley_of_fourPoint D.alphabet hdelta
  have hhyp : IsHyperbolicSpace ((delta : ℝ) + 6) W :=
    CayleyGeodesicModel.isHyperbolicSpace_pointQuot
      (CayleyGeodesicModel.isHyperbolicSpace_point D.alphabet hhypC)
  obtain ⟨sides, hsides⟩ := exists_isSideFamily hgeo points n
  have hclose : points n = points 0 := by
    -- `dsimp [points]` also unfolds `cutVertex`, and then the rewrite has no
    -- `cutVertex` left to match; `show` keeps it folded.
    show iotaG D.alphabet (cutVertex v word cut n)
      = iotaG D.alphabet (cutVertex v word cut 0)
    rw [cutVertex_last hcut v hclosed,
      cutVertex_zero hcut v]
  have hnear : ∀ s : ℕ, s < n → ∀ t : ℝ,
      t ∈ Set.Icc (0 : ℝ) (dist (points s) (points (s + 1))) →
      ∃ r : ℕ, r ≤ cut (s + 1) - cut s ∧
        dist (iotaG D.alphabet (vertex v word (cut s + r))) (sides s t) ≤ K := by
    intro s hs t ht
    obtain ⟨hseg, hseg0, hseg1⟩ := hsides s hs
    let N := cut (s + 1) - cut s
    let y : ℕ → W := fun r => iotaG D.alphabet (vertex v word (cut s + r))
    have hcs : cut s ≤ cut (s + 1) := hcut.mono s
    have hend : cut (s + 1) ≤ word.length := hcut.le_length (by omega)
    have hstep : ∀ r, r < N → dist (y r) (y (r + 1)) ≤ (2 : ℝ) := by
      intro r hr
      have hidx : cut s + (r + 1) ≤ word.length := by
        dsimp [N] at hr
        omega
      have hw : wordDist D.alphabet.carrier
          (vertex v word (cut s + r)) (vertex v word (cut s + (r + 1))) ≤ 1 := by
        have hraw := wordDist_vertex_le' D hletters v
          (show cut s + r ≤ cut s + (r + 1) by omega) hidx
        omega
      have hu := dist_iotaG_le D.alphabet
        (vertex v word (cut s + r)) (vertex v word (cut s + (r + 1)))
      dsimp [y]
      have hwR : ((wordDist D.alphabet.carrier
          (vertex v word (cut s + r)) (vertex v word (cut s + (r + 1))) : ℕ) : ℝ)
          ≤ 1 := by exact_mod_cast hw
      linarith
    have hprog : ∀ p q : ℕ, p ≤ q → q ≤ N →
        (1 / mu) * ((q - p : ℕ) : ℝ) - (b + 1) ≤ dist (y p) (y q) := by
      intro p q hpq hq
      have hp0 : cut s ≤ cut s + p := by omega
      have hpq' : cut s + p ≤ cut s + q := by omega
      have hqend : cut s + q ≤ cut (s + 1) := by
        dsimp [N] at hq
        omega
      have hprogress := hquasi s hs (cut s + p) (cut s + q)
        hp0 hpq' hqend
      have hlower := le_dist_iotaG D.alphabet
        (vertex v word (cut s + p)) (vertex v word (cut s + q))
      dsimp [y]
      have hdiff : cut s + q - (cut s + p) = q - p := by omega
      rw [hdiff] at hprogress
      have hdivide : (1 / mu) * ((q - p : ℕ) : ℝ) =
          ((q - p : ℕ) : ℝ) / mu := by ring
      rw [hdivide]
      linarith
    have hy0 : y 0 = points s := by
      dsimp [y, points, cutVertex]
    have hyN : y N = points (s + 1) := by
      dsimp [y, points, cutVertex, N]
      have harg : cut s + (cut (s + 1) - cut s) = cut (s + 1) := by omega
      rw [harg]
    exact hK W hhyp y N hstep hprog _ dist_nonneg (sides s) hseg
      (hseg0.trans hy0.symm) (hseg1.trans hyN.symm) t ht
  obtain ⟨a, b', hab, hbn, hlower, hupper, sa, hsa, sb, hsb, hcutdist⟩ :=
    Olshanskii.exists_balanced_cut hhyp hdelta0 hgeo hn hk points sides hsides hclose
  obtain ⟨ra, hra, hneara⟩ := hnear a (by omega) sa hsa
  obtain ⟨rb, hrb, hnearb⟩ := hnear b' hbn sb hsb
  let i := cut a + ra
  let j := cut b' + rb
  have hmonoa : cut a ≤ cut (a + 1) := hcut.mono a
  have hmonob : cut b' ≤ cut (b' + 1) := hcut.mono b'
  refine ⟨a, b', i, j, hab, hbn, hlower, hupper, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [i]
    omega
  · dsimp [i]
    omega
  · dsimp [j]
    omega
  · dsimp [j]
    omega
  · have hmodel : dist (iotaG D.alphabet (vertex v word i))
        (iotaG D.alphabet (vertex v word j))
        ≤ 2 * K + 6 * ((delta : ℝ) + 6) * ((k : ℝ) + 1) + 1 := by
      have htri := dist_triangle4 (iotaG D.alphabet (vertex v word i))
        (sides a sa) (sides b' sb) (iotaG D.alphabet (vertex v word j))
      have hneara' : dist (iotaG D.alphabet (vertex v word i)) (sides a sa) ≤ K := by
        simpa [i] using hneara
      have hnearb' : dist (sides b' sb) (iotaG D.alphabet (vertex v word j)) ≤ K := by
        rw [dist_comm]
        simpa [j] using hnearb
      linarith
    have hlowerModel := le_dist_iotaG D.alphabet (vertex v word i) (vertex v word j)
    have hreal : ((wordDist D.alphabet.carrier
        (vertex v word i) (vertex v word j) : ℕ) : ℝ)
        ≤ 6 * ((delta : ℝ) + 6) * ((k : ℝ) + 1) + ((⌈2 * K + 2⌉₊ : ℕ) : ℝ) := by
      have hceil : 2 * K + 2 ≤ ((⌈2 * K + 2⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
      linarith
    have hcast : ((6 * (delta + 6) * (k + 1) + ⌈2 * K + 2⌉₊ : ℕ) : ℝ)
        = 6 * ((delta : ℝ) + 6) * ((k : ℝ) + 1) + ((⌈2 * K + 2⌉₊ : ℕ) : ℝ) := by
      push_cast
      ring
    rw [← hcast] at hreal
    exact_mod_cast hreal

end GroupApproximation.GGT.DGOPolygonCut

#audit_axioms GroupApproximation.GGT.DGOPolygonCut.exists_balanced_interior_cut_word_quasi
