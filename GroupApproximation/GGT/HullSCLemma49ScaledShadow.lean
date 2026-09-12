import GroupApproximation.GGT.HullSCLemma49QuadrangleShadow
import GroupApproximation.GGT.HullSCLemma49ScaledBlocks

/-!
# Scaled shadow indices for Hull's Lemma 4.9

The long-period proof orders four shadow endpoints with a power-side
multiplicative constant `4`.  Bowditch's stable-translation bound gives an
arbitrary positive natural constant `M` in the short loxodromic branch.  This
file proves the same index estimates at `M`.

The relator exterior retains Hull's `(4,1)` constants, so a shadow index is
still at most four times its distance from the initial endpoint.  The only new
factor occurs when power-side distance is converted back to power parameter.
The scaled repeated blocks use a divisor large compared with `M`, leaving the
quarter-length middle interval larger than this conversion cost.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.WordMetric

universe u

/-! ## Generic parameter control -/

/-- A shadow index cannot run far ahead of its power parameter.  This estimate
uses only the upper half of the power chain, which is independent of its
multiplicative constant. -/
theorem Lemma49ContiguityShadow.index_upper_of_powerMu
    {G : Type u} [Group G] {Lambda : Type*}
    {D : GGT.RelGenSet G Lambda}
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n eps : ℕ} {mu : ℝ}
    {Z : Lemma49GeodesicPowerDiagram D v g n}
    {C : Lemma49RelativeGreendlingerCell D v g n eps mu Z}
    {K b : ℕ} {powerMu : ℝ}
    (Sh : Lemma49ContiguityShadow C K)
    (hRel : GGT.IsQuasiGeodesicChainAt D.alphabet.carrier 4 1
      C.exteriorVertex C.contiguity.exterior.length)
    (hPow : GGT.IsQuasiGeodesicChainAt D.alphabet.carrier powerMu b
      C.powerArcVertex C.boundaryArc.length)
    {i : ℕ} (hi : i ≤ C.boundaryArc.length) :
    Sh.index i ≤ 4 * (i + eps + K + 1) := by
  have hpowUpper := (hPow 0 i (Nat.zero_le i) hi).2
  have hleft := C.leftEndpoint_close
  have hclose := Sh.close i hi
  have htri₁ := wordDist_triangle D.alphabet.symmetricGenerating
    (C.exteriorVertex 0) (C.powerArcVertex 0) (C.powerArcVertex i)
  have htri₂ := wordDist_triangle D.alphabet.symmetricGenerating
    (C.exteriorVertex 0) (C.powerArcVertex i)
      (C.exteriorVertex (Sh.index i))
  have hdist : wordDist D.alphabet.carrier
      (C.exteriorVertex 0) (C.exteriorVertex (Sh.index i)) ≤
      eps + i + K := by
    omega
  have hdistReal :
      (wordDist D.alphabet.carrier
        (C.exteriorVertex 0) (C.exteriorVertex (Sh.index i)) : ℝ) ≤
        (eps : ℝ) + (i : ℝ) + (K : ℝ) := by
    exact_mod_cast hdist
  have hrelLower :=
    (hRel 0 (Sh.index i) (Nat.zero_le _) (Sh.index_le i hi)).1
  have hreal : (Sh.index i : ℝ) ≤
      ((4 * (i + eps + K + 1) : ℕ) : ℝ) := by
    push_cast
    norm_num at hrelLower
    linarith [hdistReal]
  exact_mod_cast hreal

/-- Far-apart power parameters have shadow indices in the same order at an
arbitrary positive natural multiplicative constant. -/
theorem Lemma49ContiguityShadow.index_strictMono_of_far_powerMu
    {G : Type u} [Group G] {Lambda : Type*}
    {D : GGT.RelGenSet G Lambda}
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n eps : ℕ} {mu : ℝ}
    {Z : Lemma49GeodesicPowerDiagram D v g n}
    {C : Lemma49RelativeGreendlingerCell D v g n eps mu Z}
    {K b powerMu : ℕ}
    (Sh : Lemma49ContiguityShadow C K) (hpowerMu : 0 < powerMu)
    (hRel : GGT.IsQuasiGeodesicChainAt D.alphabet.carrier 4 1
      C.exteriorVertex C.contiguity.exterior.length)
    (hPow : GGT.IsQuasiGeodesicChainAt D.alphabet.carrier powerMu b
      C.powerArcVertex C.boundaryArc.length)
    {x y : ℕ} (hxy : x ≤ y) (hy : y ≤ C.boundaryArc.length)
    (hfar : powerMu *
      (2 * K + b + 4 * (x + eps + K + 1)) < y - x) :
    Sh.index x < Sh.index y := by
  have hx : x ≤ C.boundaryArc.length := le_trans hxy hy
  by_contra hnot
  have hreverse : Sh.index y ≤ Sh.index x := by omega
  have hrelUpper :=
    (hRel (Sh.index y) (Sh.index x) hreverse (Sh.index_le x hx)).2
  have hrelComm := wordDist_comm D.alphabet.symmetricGenerating
    (C.exteriorVertex (Sh.index x)) (C.exteriorVertex (Sh.index y))
  have hrelDist : wordDist D.alphabet.carrier
      (C.exteriorVertex (Sh.index x)) (C.exteriorVertex (Sh.index y)) ≤
      Sh.index x - Sh.index y := by
    rw [hrelComm]
    exact hrelUpper
  have hcloseX := Sh.close x hx
  have hcloseY := Sh.close y hy
  have hcloseY' : wordDist D.alphabet.carrier
      (C.exteriorVertex (Sh.index y)) (C.powerArcVertex y) ≤ K := by
    rw [wordDist_comm D.alphabet.symmetricGenerating]
    exact hcloseY
  have htri₁ := wordDist_triangle D.alphabet.symmetricGenerating
    (C.powerArcVertex x) (C.exteriorVertex (Sh.index x))
      (C.exteriorVertex (Sh.index y))
  have htri₂ := wordDist_triangle D.alphabet.symmetricGenerating
    (C.powerArcVertex x) (C.exteriorVertex (Sh.index y))
      (C.powerArcVertex y)
  have hdistUpper : wordDist D.alphabet.carrier
      (C.powerArcVertex x) (C.powerArcVertex y) ≤
      2 * K + Sh.index x := by
    omega
  have hdistUpperReal :
      (wordDist D.alphabet.carrier
        (C.powerArcVertex x) (C.powerArcVertex y) : ℝ) ≤
        2 * (K : ℝ) + (Sh.index x : ℝ) := by
    exact_mod_cast hdistUpper
  have hpowLower := (hPow x y hxy hy).1
  have hpowerMuReal : (0 : ℝ) < (powerMu : ℝ) := by
    exact_mod_cast hpowerMu
  have hboundReal : ((y - x : ℕ) : ℝ) ≤
      (powerMu : ℝ) *
        (2 * (K : ℝ) + (Sh.index x : ℝ) + (b : ℝ)) := by
    have hdiv : ((y - x : ℕ) : ℝ) / (powerMu : ℝ) ≤
        (wordDist D.alphabet.carrier
          (C.powerArcVertex x) (C.powerArcVertex y) : ℝ) + (b : ℝ) := by
      linarith
    have hcleared := (div_le_iff₀ hpowerMuReal).mp hdiv
    nlinarith [hcleared, hdistUpperReal]
  have hbound : y - x ≤ powerMu * (2 * K + Sh.index x + b) := by
    exact_mod_cast hboundReal
  have hindex := Sh.index_upper_of_powerMu hRel hPow hx
  have hinside : 2 * K + Sh.index x + b ≤
      2 * K + b + 4 * (x + eps + K + 1) := by
    omega
  have hmul := Nat.mul_le_mul_left powerMu hinside
  omega

/-- A sufficiently long power interval cannot have coincident shadow
endpoints at an arbitrary positive natural multiplicative constant. -/
theorem Lemma49ContiguityShadow.index_ne_of_far_powerMu
    {G : Type u} [Group G] {Lambda : Type*}
    {D : GGT.RelGenSet G Lambda}
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n eps : ℕ} {mu : ℝ}
    {Z : Lemma49GeodesicPowerDiagram D v g n}
    {C : Lemma49RelativeGreendlingerCell D v g n eps mu Z}
    {K b powerMu : ℕ}
    (Sh : Lemma49ContiguityShadow C K) (hpowerMu : 0 < powerMu)
    (hPow : GGT.IsQuasiGeodesicChainAt D.alphabet.carrier powerMu b
      C.powerArcVertex C.boundaryArc.length)
    {x y : ℕ} (hxy : x ≤ y) (hy : y ≤ C.boundaryArc.length)
    (hfar : powerMu * (2 * K + b) < y - x) :
    Sh.index x ≠ Sh.index y := by
  have hx : x ≤ C.boundaryArc.length := le_trans hxy hy
  intro heq
  have hcloseX := Sh.close x hx
  have hcloseY := Sh.close y hy
  rw [heq] at hcloseX
  have hcloseY' : wordDist D.alphabet.carrier
      (C.exteriorVertex (Sh.index y)) (C.powerArcVertex y) ≤ K := by
    rw [wordDist_comm D.alphabet.symmetricGenerating]
    exact hcloseY
  have htri := wordDist_triangle D.alphabet.symmetricGenerating
    (C.powerArcVertex x) (C.exteriorVertex (Sh.index y))
      (C.powerArcVertex y)
  have hdist : wordDist D.alphabet.carrier
      (C.powerArcVertex x) (C.powerArcVertex y) ≤ 2 * K := by
    omega
  have hdistReal :
      (wordDist D.alphabet.carrier
        (C.powerArcVertex x) (C.powerArcVertex y) : ℝ) ≤ 2 * (K : ℝ) := by
    exact_mod_cast hdist
  have hpowLower := (hPow x y hxy hy).1
  have hpowerMuReal : (0 : ℝ) < (powerMu : ℝ) := by
    exact_mod_cast hpowerMu
  have hboundReal : ((y - x : ℕ) : ℝ) ≤
      (powerMu : ℝ) * (2 * (K : ℝ) + (b : ℝ)) := by
    have hdiv : ((y - x : ℕ) : ℝ) / (powerMu : ℝ) ≤
        (wordDist D.alphabet.carrier
          (C.powerArcVertex x) (C.powerArcVertex y) : ℝ) + (b : ℝ) := by
      linarith
    have hcleared := (div_le_iff₀ hpowerMuReal).mp hdiv
    nlinarith [hcleared, hdistReal]
  have hbound : y - x ≤ powerMu * (2 * K + b) := by
    exact_mod_cast hboundReal
  omega

/-- The parameter span of two shadows is bounded below by the progress of
the corresponding power interval at an arbitrary multiplicative constant. -/
theorem Lemma49ContiguityShadow.indexSpan_lower_powerMu
    {G : Type u} [Group G] {Lambda : Type*}
    {D : GGT.RelGenSet G Lambda}
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n eps : ℕ} {mu : ℝ}
    {Z : Lemma49GeodesicPowerDiagram D v g n}
    {C : Lemma49RelativeGreendlingerCell D v g n eps mu Z}
    {K b powerMu : ℕ}
    (Sh : Lemma49ContiguityShadow C K)
    (hRel : GGT.IsQuasiGeodesicChainAt D.alphabet.carrier 4 1
      C.exteriorVertex C.contiguity.exterior.length)
    (hPow : GGT.IsQuasiGeodesicChainAt D.alphabet.carrier powerMu b
      C.powerArcVertex C.boundaryArc.length)
    {x y : ℕ} (hxy : x ≤ y) (hy : y ≤ C.boundaryArc.length) :
    ((y - x : ℕ) : ℝ) / powerMu - b - 2 * K ≤
      (max (Sh.index x) (Sh.index y) -
        min (Sh.index x) (Sh.index y) : ℕ) := by
  have hx : x ≤ C.boundaryArc.length := le_trans hxy hy
  have hcloseX := Sh.close x hx
  have hcloseY := Sh.close y hy
  have hspanDist : wordDist D.alphabet.carrier
      (C.exteriorVertex (Sh.index x)) (C.exteriorVertex (Sh.index y)) ≤
      max (Sh.index x) (Sh.index y) -
        min (Sh.index x) (Sh.index y) := by
    rcases le_total (Sh.index x) (Sh.index y) with hforward | hreverse
    · simpa [Nat.max_eq_right hforward, Nat.min_eq_left hforward] using
        (hRel (Sh.index x) (Sh.index y) hforward (Sh.index_le y hy)).2
    · have hraw :=
        (hRel (Sh.index y) (Sh.index x) hreverse (Sh.index_le x hx)).2
      rw [wordDist_comm D.alphabet.symmetricGenerating] at hraw
      simpa [Nat.max_eq_left hreverse, Nat.min_eq_right hreverse] using hraw
  have hcloseY' : wordDist D.alphabet.carrier
      (C.exteriorVertex (Sh.index y)) (C.powerArcVertex y) ≤ K := by
    rw [wordDist_comm D.alphabet.symmetricGenerating]
    exact hcloseY
  have htri₁ := wordDist_triangle D.alphabet.symmetricGenerating
    (C.powerArcVertex x) (C.exteriorVertex (Sh.index x))
      (C.exteriorVertex (Sh.index y))
  have htri₂ := wordDist_triangle D.alphabet.symmetricGenerating
    (C.powerArcVertex x) (C.exteriorVertex (Sh.index y))
      (C.powerArcVertex y)
  have hdistUpper : wordDist D.alphabet.carrier
      (C.powerArcVertex x) (C.powerArcVertex y) ≤
      2 * K + (max (Sh.index x) (Sh.index y) -
        min (Sh.index x) (Sh.index y)) := by
    omega
  have hdistUpperReal :
      (wordDist D.alphabet.carrier
        (C.powerArcVertex x) (C.powerArcVertex y) : ℝ) ≤
        2 * (K : ℝ) +
          (max (Sh.index x) (Sh.index y) -
            min (Sh.index x) (Sh.index y) : ℕ) := by
    exact_mod_cast hdistUpper
  have hpowLower := (hPow x y hxy hy).1
  linarith [hdistUpperReal]

/-! ## The scaled block budget -/

/-- The order-preservation error at the start of a power arc. -/
def lemma49PowerShadowError (powerMu b K eps : ℕ) : ℕ :=
  powerMu * (2 * K + b + 4 * (eps + K + 1))

/-- A scaled repeated block is longer than the initial shadow-order error. -/
theorem Lemma49ScaledRepeatedBoundaryBlocks.block_shadow_far
    {Alpha : Type*} {arc : List Alpha} {divisor powerMu b K eps : ℕ}
    (B : Lemma49ScaledRepeatedBoundaryBlocks Alpha arc divisor)
    (hdivisor : 0 < divisor)
    (hscale : divisor * (lemma49PowerShadowError powerMu b K eps + 1) ≤
      arc.length) :
    lemma49PowerShadowError powerMu b K eps < B.block.length := by
  have hquotient : lemma49PowerShadowError powerMu b K eps + 1 ≤
      arc.length / divisor := by
    apply (Nat.le_div_iff_mul_le hdivisor).2
    simpa only [Nat.mul_comm] using hscale
  rw [B.block_length]
  omega

/-- If the divisor dominates `M`, the quarter-length middle interval is
longer than the shadow-order error at the end of the first block. -/
theorem Lemma49ScaledRepeatedBoundaryBlocks.middle_shadow_far
    {Alpha : Type*} {arc : List Alpha} {divisor powerMu b K eps : ℕ}
    (B : Lemma49ScaledRepeatedBoundaryBlocks Alpha arc divisor)
    (hdivisorMu : 32 * powerMu ≤ divisor) (hdivisorEight : 8 ≤ divisor)
    (hscale : divisor * (lemma49PowerShadowError powerMu b K eps + 1) ≤
      arc.length) :
    powerMu * (2 * K + b +
      4 * (B.block.length + eps + K + 1)) < B.middle.length := by
  have hblockBudget : divisor * B.block.length ≤ arc.length := by
    rw [B.block_length]
    simpa [Nat.mul_comm] using Nat.div_mul_le_self arc.length divisor
  have hmuBlock : 32 * powerMu * B.block.length ≤ arc.length := by
    have hmul := Nat.mul_le_mul_right B.block.length hdivisorMu
    calc
      32 * powerMu * B.block.length ≤ divisor * B.block.length := by
        simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmul
      _ ≤ arc.length := hblockBudget
  have herrorBudget :
      8 * (lemma49PowerShadowError powerMu b K eps + 1) ≤ arc.length := by
    have hmul := Nat.mul_le_mul_right
      (lemma49PowerShadowError powerMu b K eps + 1) hdivisorEight
    exact le_trans (by
      simpa only [Nat.mul_comm] using hmul) hscale
  have hquarterBudget :
      4 * (lemma49PowerShadowError powerMu b K eps +
        4 * powerMu * B.block.length + 1) ≤ arc.length := by
    have hmuBlock' : 8 * (4 * powerMu * B.block.length) ≤ arc.length := by
      calc
        8 * (4 * powerMu * B.block.length) =
            32 * powerMu * B.block.length := by ring
        _ ≤ arc.length := hmuBlock
    have htwice : 2 *
        (4 * (lemma49PowerShadowError powerMu b K eps +
          4 * powerMu * B.block.length + 1)) ≤ 2 * arc.length := by
      calc
        2 * (4 * (lemma49PowerShadowError powerMu b K eps +
            4 * powerMu * B.block.length + 1)) =
            8 * (lemma49PowerShadowError powerMu b K eps + 1) +
              8 * (4 * powerMu * B.block.length) := by ring
        _ ≤ arc.length + arc.length :=
          Nat.add_le_add herrorBudget hmuBlock'
        _ = 2 * arc.length := by ring
    exact Nat.le_of_mul_le_mul_left htwice (by omega)
  have hquarter : lemma49PowerShadowError powerMu b K eps +
      4 * powerMu * B.block.length + 1 ≤ arc.length / 4 := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 4)).2
    simpa only [Nat.mul_comm] using hquarterBudget
  have hmiddle : lemma49PowerShadowError powerMu b K eps +
      4 * powerMu * B.block.length + 1 ≤ B.middle.length :=
    le_trans hquarter B.middle_long
  have hformula : powerMu * (2 * K + b +
      4 * (B.block.length + eps + K + 1)) =
      lemma49PowerShadowError powerMu b K eps +
        4 * powerMu * B.block.length := by
    dsimp [lemma49PowerShadowError]
    ring
  rw [hformula]
  omega

/-! ## Numerical check -/

/-- The scaled divisor inequalities have a concrete model with `M > 4`. -/
theorem scaledShadow_parameters_model :
    32 * 7 ≤ 800 ∧ 8 ≤ 800 ∧
      7 * (2 * 3 + 12 + 4 * (5 + 3 + 1)) < 400 := by
  norm_num

end HullSC
end GroupApproximation
