import GroupApproximation.GGT.HullSCLemma49PrimePiece
import GroupApproximation.GGT.HullSCLemma49ScaledShadow

/-!
# Scaled prime pieces in Hull's Lemma 4.9

The short loxodromic branch has a power-boundary multiplicative constant `M`
and uses periodic blocks of relative size `1/Q`.  This file proves the
quantitative part of Osin Lemma 6.3 at those constants.

The two shadow intervals have length at least the block progress divided by
`M`, less the chain and connector errors.  Taking the final
small-cancellation coefficient to be `1/(100000*M*Q)` leaves ample room for
those losses.  The relator threshold is chosen after `M`, `Q`, and the shadow
constant, exactly as in Hull's proof.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.WordMetric

universe u

/-! ## The scaled final coefficient -/

/-- The final `C₁` coefficient used by a power-side constant `M` and block
divisor `Q`. -/
def lemma49ScaledFinalMu (powerMu divisor : ℕ) : ℝ :=
  1 / (100000 * powerMu * divisor : ℕ)

/-- The scaled coefficient is positive when both natural parameters are
positive. -/
theorem lemma49ScaledFinalMu_pos {powerMu divisor : ℕ}
    (hpowerMu : 0 < powerMu) (hdivisor : 0 < divisor) :
    0 < lemma49ScaledFinalMu powerMu divisor := by
  dsimp [lemma49ScaledFinalMu]
  positivity

/-! ## Endpoint values of the two scaled blocks -/

/-- The first two power-arc endpoints span the first scaled block. -/
theorem Lemma49ScaledRepeatedBoundaryBlocks.first_powerArc_span
    {G : Type u} [Group G] {Lambda : Type*}
    {D : GGT.RelGenSet G Lambda}
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n eps : ℕ} {mu : ℝ}
    {Z : Lemma49GeodesicPowerDiagram D v g n}
    (C : Lemma49RelativeGreendlingerCell D v g n eps mu Z)
    {divisor : ℕ}
    (B : Lemma49ScaledRepeatedBoundaryBlocks
      (GGT.RelLetter G Lambda) C.boundaryArc divisor) :
    (C.powerArcVertex 0)⁻¹ * C.powerArcVertex B.block.length =
      GGT.RelLetter.listVal B.block := by
  have htake : C.boundaryArc.take B.block.length = B.block := by
    calc
      C.boundaryArc.take B.block.length =
          (B.block ++ B.middle ++ B.block ++ B.tail).take B.block.length :=
        congrArg (List.take B.block.length) B.decomposition
      _ = B.block := by
        simpa only [List.append_assoc] using
          (List.take_left :
            (B.block ++ (B.middle ++ B.block ++ B.tail)).take
                B.block.length = B.block)
  simp only [Lemma49RelativeGreendlingerCell.powerArcVertex, List.take_zero,
    GGT.RelLetter.listVal_nil, mul_one, htake]
  group

/-- The later two power-arc endpoints span the second copy of the scaled
block. -/
theorem Lemma49ScaledRepeatedBoundaryBlocks.second_powerArc_span
    {G : Type u} [Group G] {Lambda : Type*}
    {D : GGT.RelGenSet G Lambda}
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n eps : ℕ} {mu : ℝ}
    {Z : Lemma49GeodesicPowerDiagram D v g n}
    (C : Lemma49RelativeGreendlingerCell D v g n eps mu Z)
    {divisor : ℕ}
    (B : Lemma49ScaledRepeatedBoundaryBlocks
      (GGT.RelLetter G Lambda) C.boundaryArc divisor) :
    (C.powerArcVertex (B.block.length + B.middle.length))⁻¹ *
        C.powerArcVertex
          (B.block.length + B.middle.length + B.block.length) =
      GGT.RelLetter.listVal B.block := by
  have htake₂ : C.boundaryArc.take (B.block.length + B.middle.length) =
      B.block ++ B.middle := by
    calc
      C.boundaryArc.take (B.block.length + B.middle.length) =
          (B.block ++ B.middle ++ B.block ++ B.tail).take
            (B.block.length + B.middle.length) :=
        congrArg (List.take (B.block.length + B.middle.length))
          B.decomposition
      _ = B.block ++ B.middle := by
        simpa only [List.length_append, List.append_assoc] using
          (List.take_left :
            ((B.block ++ B.middle) ++ (B.block ++ B.tail)).take
                (B.block ++ B.middle).length = B.block ++ B.middle)
  have htake₃ : C.boundaryArc.take
      (B.block.length + B.middle.length + B.block.length) =
      B.block ++ B.middle ++ B.block := by
    calc
      C.boundaryArc.take
          (B.block.length + B.middle.length + B.block.length) =
          (B.block ++ B.middle ++ B.block ++ B.tail).take
            (B.block.length + B.middle.length + B.block.length) :=
        congrArg
          (List.take (B.block.length + B.middle.length + B.block.length))
          B.decomposition
      _ = B.block ++ B.middle ++ B.block := by
        simpa only [List.length_append] using
          (List.take_left :
            ((B.block ++ B.middle ++ B.block) ++ B.tail).take
                (B.block ++ B.middle ++ B.block).length =
              B.block ++ B.middle ++ B.block)
  simp only [Lemma49RelativeGreendlingerCell.powerArcVertex, htake₂, htake₃,
    RelWord.listVal_append]
  group

/-! ## Relator and boundary-arc scales -/

/-- A sufficiently large relator threshold makes the selected boundary arc
dominate any prescribed integral target. -/
theorem Lemma49RelativeGreendlingerCell.boundaryArc_scaled_scale
    {G : Type u} [Group G] {Lambda : Type*}
    {D : GGT.RelGenSet G Lambda}
    {v : List (GGT.RelLetter G Lambda)} {g : G}
    {n eps rho divisor target : ℕ}
    {Z : Lemma49GeodesicPowerDiagram D v g n}
    (C : Lemma49RelativeGreendlingerCell D v g n eps (1 / 1000) Z)
    (hinput : RelWord.IsLemma49Input D (RelWord.symmetrized v)
      eps (1 / 1000) rho)
    (hscale : 1000 * divisor * (target + 2 * eps + 2) ≤ rho) :
    divisor * target ≤ C.boundaryArc.length := by
  have hrelatorScaleNat :
      1000 * divisor * (target + 2 * eps + 2) ≤ C.relator.length :=
    le_trans hscale (hinput.long C.relator C.relator_mem)
  have hrelatorScale :
      (1000 : ℝ) * (divisor : ℝ) *
          ((target : ℝ) + 2 * (eps : ℝ) + 2) ≤
        (C.relator.length : ℝ) := by
    exact_mod_cast hrelatorScaleNat
  have hexterior := C.exterior_large
  have harc := C.boundaryArc_lower hinput
  have htarget : (divisor : ℝ) * (target : ℝ) ≤
      (C.boundaryArc.length : ℝ) := by
    norm_num at hexterior
    have hdivisorNonneg : (0 : ℝ) ≤ (divisor : ℝ) := by positivity
    have htargetNonneg : (0 : ℝ) ≤ (target : ℝ) := by positivity
    have hepsNonneg : (0 : ℝ) ≤ (eps : ℝ) := by positivity
    nlinarith
  exact_mod_cast htarget

/-- Once the relator absorbs the two connector errors, it is at most one
hundred times the opposite boundary arc. -/
theorem Lemma49RelativeGreendlingerCell.relator_length_le_boundaryArc
    {G : Type u} [Group G] {Lambda : Type*}
    {D : GGT.RelGenSet G Lambda}
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n eps rho : ℕ}
    {Z : Lemma49GeodesicPowerDiagram D v g n}
    (C : Lemma49RelativeGreendlingerCell D v g n eps (1 / 1000) Z)
    (hinput : RelWord.IsLemma49Input D (RelWord.symmetrized v)
      eps (1 / 1000) rho)
    (hscale : 1000 * (2 * eps + 2) ≤ rho) :
    C.relator.length ≤ 100 * C.boundaryArc.length := by
  have hrelatorScaleNat : 1000 * (2 * eps + 2) ≤ C.relator.length :=
    le_trans hscale (hinput.long C.relator C.relator_mem)
  have hrelatorScale :
      (1000 : ℝ) * (2 * (eps : ℝ) + 2) ≤
        (C.relator.length : ℝ) := by
    exact_mod_cast hrelatorScaleNat
  have hexterior := C.exterior_large
  have harc := C.boundaryArc_lower hinput
  have htarget : (C.relator.length : ℝ) ≤
      100 * (C.boundaryArc.length : ℝ) := by
    norm_num at hexterior
    linarith
  exact_mod_cast htarget

/-! ## Size of a scaled shadow interval -/

/-- Every shadow interval corresponding to one scaled repeated block clears
the final coefficient `1/(100000*M*Q)`. -/
theorem Lemma49ContiguityShadow.scaledRepeatedBlock_indexSpan_large
    {G : Type u} [Group G] {Lambda : Type*}
    {D : GGT.RelGenSet G Lambda}
    {v : List (GGT.RelLetter G Lambda)} {g : G}
    {n eps rho b K powerMu divisor : ℕ}
    {Z : Lemma49GeodesicPowerDiagram D v g n}
    {C : Lemma49RelativeGreendlingerCell D v g n eps (1 / 1000) Z}
    (Sh : Lemma49ContiguityShadow C K)
    (B : Lemma49ScaledRepeatedBoundaryBlocks
      (GGT.RelLetter G Lambda) C.boundaryArc divisor)
    (hinput : RelWord.IsLemma49Input D (RelWord.symmetrized v)
      eps (1 / 1000) rho)
    (hRel : GGT.IsQuasiGeodesicChainAt D.alphabet.carrier 4 1
      C.exteriorVertex C.contiguity.exterior.length)
    (hPow : GGT.IsQuasiGeodesicChainAt D.alphabet.carrier powerMu b
      C.powerArcVertex C.boundaryArc.length)
    (hpowerMu : 0 < powerMu) (hdivisor : 0 < divisor)
    (hArcScale : divisor *
      (2 * lemma49PowerShadowError powerMu b K eps + 2) ≤
        C.boundaryArc.length)
    (hRelatorScale : 1000 * (2 * eps + 2) ≤ rho)
    {x y : ℕ} (hxy : x ≤ y) (hy : y ≤ C.boundaryArc.length)
    (hgap : y - x = B.block.length) :
    lemma49ScaledFinalMu powerMu divisor * (C.relator.length : ℝ) ≤
      (max (Sh.index x) (Sh.index y) -
        min (Sh.index x) (Sh.index y) : ℕ) := by
  have hspan := Sh.indexSpan_lower_powerMu hRel hPow hxy hy
  have hblockHuge :
      2 * lemma49PowerShadowError powerMu b K eps + 2 ≤ B.block.length := by
    rw [B.block_length]
    apply (Nat.le_div_iff_mul_le hdivisor).2
    simpa only [Nat.mul_comm] using hArcScale
  have hinner : b + 2 * K ≤ 2 * K + b + 4 * (eps + K + 1) := by omega
  have hbaseMul := Nat.mul_le_mul_left powerMu hinner
  have herrorBase : powerMu * (b + 2 * K) ≤
      lemma49PowerShadowError powerMu b K eps := by
    exact hbaseMul
  have hblockBase : 2 * (powerMu * (b + 2 * K)) + 2 ≤
      B.block.length := by
    omega
  have hrelatorArc := C.relator_length_le_boundaryArc hinput hRelatorScale
  have hmod : C.boundaryArc.length % divisor < divisor :=
    Nat.mod_lt _ hdivisor
  have hdecomp := Nat.div_add_mod C.boundaryArc.length divisor
  have harcDiv : C.boundaryArc.length <
      (C.boundaryArc.length / divisor + 1) * divisor := by
    rw [Nat.add_mul, one_mul]
    rw [Nat.mul_comm divisor (C.boundaryArc.length / divisor)] at hdecomp
    omega
  have harcBlock : C.boundaryArc.length <
      (B.block.length + 1) * divisor := by
    rwa [B.block_length]
  have hrelatorBlock : C.relator.length ≤
      100 * divisor * (B.block.length + 1) := by
    calc
      C.relator.length ≤ 100 * C.boundaryArc.length := hrelatorArc
      _ ≤ 100 * ((B.block.length + 1) * divisor) :=
        Nat.mul_le_mul_left 100 harcBlock.le
      _ = 100 * divisor * (B.block.length + 1) := by ring
  have hpowerMuReal : (0 : ℝ) < (powerMu : ℝ) := by
    exact_mod_cast hpowerMu
  have hdivisorReal : (0 : ℝ) < (divisor : ℝ) := by
    exact_mod_cast hdivisor
  have hrelatorBlockReal : (C.relator.length : ℝ) ≤
      100 * (divisor : ℝ) * ((B.block.length : ℝ) + 1) := by
    exact_mod_cast hrelatorBlock
  have hsmall : lemma49ScaledFinalMu powerMu divisor *
      (C.relator.length : ℝ) ≤
      ((B.block.length : ℝ) + 1) / (1000 * (powerMu : ℝ)) := by
    have hden : (0 : ℝ) < 100000 * (powerMu : ℝ) * (divisor : ℝ) := by
      positivity
    have hdivided := (div_le_div_iff_of_pos_right hden).2 hrelatorBlockReal
    have heq :
        (100 * (divisor : ℝ) * ((B.block.length : ℝ) + 1)) /
            (100000 * (powerMu : ℝ) * (divisor : ℝ)) =
          ((B.block.length : ℝ) + 1) / (1000 * (powerMu : ℝ)) := by
      field_simp
      ring
    rw [heq] at hdivided
    calc
      lemma49ScaledFinalMu powerMu divisor * (C.relator.length : ℝ) =
          (C.relator.length : ℝ) /
            (100000 * (powerMu : ℝ) * (divisor : ℝ)) := by
        dsimp [lemma49ScaledFinalMu]
        push_cast
        ring
      _ ≤ ((B.block.length : ℝ) + 1) /
          (1000 * (powerMu : ℝ)) := hdivided
  have hblockBaseReal :
      2 * ((powerMu : ℝ) * ((b : ℝ) + 2 * (K : ℝ))) + 2 ≤
        (B.block.length : ℝ) := by
    exact_mod_cast hblockBase
  have hsmallProgress :
      ((B.block.length : ℝ) + 1) / (1000 * (powerMu : ℝ)) ≤
        (B.block.length : ℝ) / (powerMu : ℝ) - (b : ℝ) - 2 * (K : ℝ) := by
    rw [div_le_iff₀ hpowerMuReal]
    have hthousand : (0 : ℝ) < 1000 := by norm_num
    have haux : ((B.block.length : ℝ) + 1) / 1000 ≤
        (B.block.length : ℝ) -
          (powerMu : ℝ) * ((b : ℝ) + 2 * (K : ℝ)) := by
      rw [div_le_iff₀ hthousand]
      nlinarith
    nlinarith
  rw [hgap] at hspan
  exact le_trans hsmall (le_trans hsmallProgress hspan)

/-! ## Model check -/

/-- The scaled coefficient is nonzero in a concrete short-power model. -/
theorem lemma49ScaledFinalMu_model :
    0 < lemma49ScaledFinalMu 7 800 := by
  exact lemma49ScaledFinalMu_pos (by omega) (by omega)

end HullSC
end GroupApproximation
