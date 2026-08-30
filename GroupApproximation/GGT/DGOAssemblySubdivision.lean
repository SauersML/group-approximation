import GroupApproximation.GGT.DGOAssemblyLetters
import GroupApproximation.GGT.ElementaryMorseChord
import GroupApproximation.GGT.OsinGeodesicWord

/-!
# The quantitative subdivision supplied by a balanced cut

The preceding assembly modules construct the two closed words, their polygon
cuts, and the dictionaries which identify their arc vertices and letters with
those of the original polygon.  This module records the numerical content of
that construction in the form used by DGO's subdivision recursion.

If the selected graph vertices lie on balanced sides `a < b` and the geodesic
chord has `L` letters, then inserting those vertices gives side counts

* `m₁ = (b - a + 1) + L`, and
* `m₂ = (n - b) + a + 1 + L`.

Consequently `m₁ + m₂ = n + 2 + 2L`.  The two quarter-separation
inequalities say, without any division or rounding,

* `4m₁ ≤ 3n + 4 + 4L`, and
* `4m₂ ≤ 3n + 4 + 4L`.

`exists_interior_half_polygon_data` inserts the vertices with `splitPairCut` and
applies the existing corner assembly to the refined `(n+2)`-gon.  The price is
exactly two sides and is independent of the lengths of the original sides, as
in DGO Lemma 4.20.  The obsolete bounded-side corner-pullback wrapper has been
retired rather than retained as a parallel API.

After this refinement, the remaining Proposition 4.14 work is the component
transfer across the chord and the addition of the witnesses supplied by the
smaller polygons.  The geometric selection theorem must supply the two close
graph vertices; it no longer owes a bound on every side.
-/

namespace GroupApproximation
namespace GGT
namespace DGOPolygonCut

open GroupApproximation.GGT.OsinComponents
open GroupApproximation.WordMetric
open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

variable {G : Type u} [Group G] {Lambda : Type w}

/-! ## The side-count arithmetic -/

/-- **An interior cut pays two sides, not two side lengths.**

If the selected vertices lie on sides `a < b`, inserting them makes the two
arc counts `b-a+1` and `n-b+a+1`.  Consequently the two half-polygons have
total side count `n+2+2L`, and the quarter-separation estimates acquire only
the constant `4` before the chord contribution. -/
theorem interior_half_side_count_bounds {n a b L : ℕ} (hab : a < b) (hbn : b < n)
    (hlower : n ≤ 4 * (b - a)) (hupper : 4 * (b - a) ≤ 3 * n) :
    ((b - a + 1) + L) + ((n - b) + a + 1 + L) = n + 2 + 2 * L ∧
      4 * ((b - a + 1) + L) ≤ 3 * n + 4 + 4 * L ∧
      4 * ((n - b) + a + 1 + L) ≤ 3 * n + 4 + 4 * L := by
  omega

/-! ## The interior refinement -/

/-- **DGO Lemma 4.20's balanced cut at graph vertices.**

For fixed hyperbolicity and quasi-geodesic constants there is an additive
constant `R` such that every closed `(1,b)`-quasi-geodesic `n`-gon has
quarter-separated sides containing vertices at distance at most
`6(δ+6)(k+1)+R`, whenever `n ≤ 2^k`.

The bisection itself is applied to geodesic replacements of the sides in
`CayleyGeodesicModel.PointQuot`.  The uniform chord-near-chain half of Morse
then moves each selected point back to a vertex of the corresponding original
side.  This is the step that removes the old dependence on the lengths of
those sides. -/
theorem exists_balanced_interior_cut_word (D : RelGenSet G Lambda) {delta b : ℕ}
    (hdelta : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) :
    ∃ R : ℕ, ∀ {n k : ℕ}, 8 ≤ n → n ≤ 2 ^ k → ∀ (v : G)
      (word : List (RelLetter G Lambda)) (cut : ℕ → ℕ),
      IsCutPolygon D (b : ℝ) n v word cut →
      ∃ a b' i j : ℕ, a < b' ∧ b' < n ∧
        n ≤ 4 * (b' - a) ∧ 4 * (b' - a) ≤ 3 * n ∧
        cut a ≤ i ∧ i ≤ cut (a + 1) ∧
        cut b' ≤ j ∧ j ≤ cut (b' + 1) ∧
        wordDist D.alphabet.carrier (vertex v word i) (vertex v word j)
          ≤ 6 * (delta + 6) * (k + 1) + R := by
  have hdelta0 : (0 : ℝ) ≤ (delta : ℝ) + 6 := by positivity
  obtain ⟨K, hK0, hK⟩ :=
    ElementaryMorse.exists_bound_chord_near_chain_uniform
      (δ := (delta : ℝ) + 6) (D := 2) (l := 1) (B := (b : ℝ) + 1)
      hdelta0 (by positivity) (by norm_num) (by positivity)
  refine ⟨⌈2 * K + 2⌉₊, ?_⟩
  intro n k hn hk v word cut hpolygon
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
    rw [cutVertex_last hpolygon.cut v hpolygon.closed,
      cutVertex_zero hpolygon.cut v]
  have hnear : ∀ s : ℕ, s < n → ∀ t : ℝ,
      t ∈ Set.Icc (0 : ℝ) (dist (points s) (points (s + 1))) →
      ∃ r : ℕ, r ≤ cut (s + 1) - cut s ∧
        dist (iotaG D.alphabet (vertex v word (cut s + r))) (sides s t) ≤ K := by
    intro s hs t ht
    obtain ⟨hseg, hseg0, hseg1⟩ := hsides s hs
    let N := cut (s + 1) - cut s
    let y : ℕ → W := fun r => iotaG D.alphabet (vertex v word (cut s + r))
    have hcs : cut s ≤ cut (s + 1) := hpolygon.cut.mono s
    have hend : cut (s + 1) ≤ word.length := hpolygon.cut.le_length (by omega)
    have hstep : ∀ r, r < N → dist (y r) (y (r + 1)) ≤ (2 : ℝ) := by
      intro r hr
      have hidx : cut s + (r + 1) ≤ word.length := by
        dsimp [N] at hr
        omega
      have hw : wordDist D.alphabet.carrier
          (vertex v word (cut s + r)) (vertex v word (cut s + (r + 1))) ≤ 1 := by
        have hraw := wordDist_vertex_le' D hpolygon.letters v
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
        (1 : ℝ) * ((q - p : ℕ) : ℝ) - ((b : ℝ) + 1) ≤ dist (y p) (y q) := by
      intro p q hpq hq
      have hp0 : cut s ≤ cut s + p := by omega
      have hpq' : cut s + p ≤ cut s + q := by omega
      have hqend : cut s + q ≤ cut (s + 1) := by
        dsimp [N] at hq
        omega
      have hquasi := hpolygon.quasi s hs (cut s + p) (cut s + q)
        hp0 hpq' hqend
      have hlower := le_dist_iotaG D.alphabet
        (vertex v word (cut s + p)) (vertex v word (cut s + q))
      dsimp [y]
      have hdiff : cut s + q - (cut s + p) = q - p := by omega
      rw [hdiff] at hquasi
      rw [one_mul]
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
  have hmonoa : cut a ≤ cut (a + 1) := hpolygon.cut.mono a
  have hmonob : cut b' ≤ cut (b' + 1) := hpolygon.cut.mono b'
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

/-- **Two close graph vertices inside quarter-separated sides produce the two
balanced half-polygons, with no side-length hypothesis.**

The hypotheses through `hjb` say that `i` and `j` are vertices on the selected
sides `a` and `b`.  `splitPairCut` inserts them as corners `a+1` and `b+2` of an
`(n+2)`-gon.  From that point onward this theorem uses the existing
corner-to-corner half words, cut functions, closure proofs, and admissibility
proofs unchanged.

This is the combinatorial content of the interior-point move in DGO Lemma
4.20.  Its caller still has to select `i,j` with `hdist` bounded logarithmically;
no uniform bound on the lengths `cut (s+1)-cut s` occurs here. -/
theorem exists_interior_half_polygon_data (D : RelGenSet G Lambda)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {n : ℕ} {q : ℝ}
    (v : G) (word : List (RelLetter G Lambda)) (cut : ℕ → ℕ)
    (hpolygon : IsCutPolygon D q n v word cut)
    {a b i j L : ℕ} (hab : a < b) (hbn : b < n)
    (hlower : n ≤ 4 * (b - a)) (hupper : 4 * (b - a) ≤ 3 * n)
    (hai : cut a ≤ i) (hia : i ≤ cut (a + 1))
    (hbj : cut b ≤ j) (hjb : j ≤ cut (b + 1))
    (hdist : wordDist D.alphabet.carrier (vertex v word i) (vertex v word j) ≤ L) :
    ∃ chord : List (RelLetter G Lambda), ∃ cut1 cut2 : ℕ → ℕ,
      IsGeodesicWord D (vertex v word i) (vertex v word j) chord ∧
      IsPolygonCut ((b - a + 1) + chord.length)
        (firstHalf word (splitPairCut cut a b i j) (a + 1) (b + 2) chord) cut1 ∧
      IsPolygonCut ((n - b) + a + 1 + chord.length)
        (secondHalf word (splitPairCut cut a b i j) (a + 1) (b + 2) chord) cut2 ∧
      RelLetter.listVal
          (firstHalf word (splitPairCut cut a b i j) (a + 1) (b + 2) chord) = 1 ∧
      RelLetter.listVal
          (secondHalf word (splitPairCut cut a b i j) (a + 1) (b + 2) chord) = 1 ∧
      (∀ x ∈ firstHalf word (splitPairCut cut a b i j) (a + 1) (b + 2) chord,
        D.IsLetter x) ∧
      (∀ x ∈ secondHalf word (splitPairCut cut a b i j) (a + 1) (b + 2) chord,
        D.IsLetter x) ∧
      chord.length ≤ L ∧
      ((((b - a + 1) + chord.length) +
          ((n - b) + a + 1 + chord.length) = n + 2 + 2 * chord.length) ∧
        4 * ((b - a + 1) + chord.length) ≤ 3 * n + 4 + 4 * chord.length ∧
        4 * ((n - b) + a + 1 + chord.length) ≤ 3 * n + 4 + 4 * chord.length) := by
  let refined := splitPairCut cut a b i j
  let A := a + 1
  let B := b + 2
  have hrefined : IsPolygonCut (n + 2) word refined := by
    simpa [refined] using
      isPolygonCut_splitPair hpolygon.cut hab hbn hai hia hbj hjb
  have hAB : A < B := by dsimp [A, B]; omega
  have hBN : B < n + 2 := by dsimp [B]; omega
  have hBA : B - A = b - a + 1 := by dsimp [A, B]; omega
  have hsecondCount : (n + 2 - B) + A = (n - b) + a + 1 := by
    dsimp [A, B]
    omega
  obtain ⟨chord, hchord⟩ :=
    existsGeodesicWord D (vertex v word i) (vertex v word j)
  let cut1 : ℕ → ℕ :=
    appendCut (fun s => refined (A + s) - refined A) (B - A) (fun s => s)
  let cut2 : ℕ → ℕ :=
    appendCut (appendCut (fun s => refined (B + s) - refined B)
      (n + 2 - B) refined) ((n + 2 - B) + A) (fun s => s)
  have hrvA : cutVertex v word refined A = vertex v word i := by
    have h := cutVertex_splitPair_left v word cut (i := i) (j := j) hab
    simp only [refined, A]
    exact h
  have hrvB : cutVertex v word refined B = vertex v word j := by
    have h := cutVertex_splitPair_right v word cut a b i j
    simp only [refined, B]
    exact h
  have hchord_value : RelLetter.listVal chord =
      (cutVertex v word refined A)⁻¹ * cutVertex v word refined B := by
    rw [hrvA, hrvB, ← hchord.2.1]
    group
  have hfirst_closed : RelLetter.listVal (firstHalf word refined A B chord) = 1 :=
    listVal_firstHalf word v refined (hrefined.mono_le (Nat.le_of_lt hAB))
      hchord_value
  have hsecond_closed : RelLetter.listVal (secondHalf word refined A B chord) = 1 :=
    listVal_secondHalf word v refined (hrefined.le_length (by omega))
      hpolygon.closed hchord_value
  have hcounts := interior_half_side_count_bounds hab hbn hlower hupper
    (L := chord.length)
  refine ⟨chord, cut1, cut2, hchord, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hcounts⟩
  · have hcut := isPolygonCut_firstHalf hrefined (Nat.le_of_lt hAB)
      (Nat.le_of_lt hBN) chord
    rw [hBA] at hcut
    simp only [refined, A, B, cut1]
    convert hcut using 3
  · have hcut := isPolygonCut_secondHalf hrefined (by omega : A ≤ n + 2)
      (Nat.le_of_lt hBN) chord
    rw [hsecondCount] at hcut
    simp only [refined, A, B, cut2]
    convert hcut using 3
  · simpa [refined, A, B] using hfirst_closed
  · simpa [refined, A, B] using hsecond_closed
  · simpa [refined, A, B] using
      (isLetter_firstHalf D hsymm hpolygon.letters hchord.1 refined A B)
  · simpa [refined, A, B] using
      (isLetter_secondHalf D hpolygon.letters hchord.1 refined A B)
  · rw [hchord.2.2]
    exact hdist

end DGOPolygonCut
end GGT
end GroupApproximation
