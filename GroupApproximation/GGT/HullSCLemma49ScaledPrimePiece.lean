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
noncomputable def lemma49ScaledFinalMu (powerMu divisor : ℕ) : ℝ :=
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
    (hdivisor : 0 < divisor)
    (hscale : 1000 * divisor * (target + 2 * eps + 2) ≤ rho) :
    divisor * target ≤ C.boundaryArc.length := by
  rcases Nat.eq_zero_or_pos target with rfl | htargetPos
  · simp
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
    have hdivisorReal : (1 : ℝ) ≤ (divisor : ℝ) := by exact_mod_cast hdivisor
    have htargetReal : (1 : ℝ) ≤ (target : ℝ) := by exact_mod_cast htargetPos
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
    have hthousand : (0 : ℝ) < 1000 := by norm_num
    have haux : ((B.block.length : ℝ) + 1) / 1000 ≤
        (B.block.length : ℝ) -
          (powerMu : ℝ) * ((b : ℝ) + 2 * (K : ℝ)) := by
      rw [div_le_iff₀ hthousand]
      nlinarith
    have hdivided := (div_le_div_iff_of_pos_right hpowerMuReal).2 haux
    calc
      ((B.block.length : ℝ) + 1) / (1000 * (powerMu : ℝ)) =
          (((B.block.length : ℝ) + 1) / 1000) / (powerMu : ℝ) := by
        field_simp
      _ ≤ ((B.block.length : ℝ) -
          (powerMu : ℝ) * ((b : ℝ) + 2 * (K : ℝ))) /
            (powerMu : ℝ) := hdivided
      _ = (B.block.length : ℝ) / (powerMu : ℝ) -
          (b : ℝ) - 2 * (K : ℝ) := by
        field_simp
        ring
  rw [hgap] at hspan
  exact le_trans hsmall (le_trans hsmallProgress hspan)

/-! ## The scaled prime-piece contradiction -/

/-- Two scaled repeated boundary blocks contradict the final prime-piece
clause.  This is the non-Greendlinger content of Osin Lemma 6.3 at an
arbitrary positive natural power-side constant. -/
theorem false_of_lemma49ScaledLongArc_contiguityShadow
    {G : Type u} [Group G] {Lambda : Type*}
    {D : GGT.RelGenSet G Lambda}
    {v : List (GGT.RelLetter G Lambda)} {g : G}
    {n eps epsFinal rho b K powerMu divisor : ℕ}
    {Z : Lemma49GeodesicPowerDiagram D v g n}
    (C : Lemma49RelativeGreendlingerCell D v g n eps (1 / 1000) Z)
    (B : Lemma49ScaledRepeatedBoundaryBlocks
      (GGT.RelLetter G Lambda) C.boundaryArc divisor)
    (Sh : Lemma49ContiguityShadow C K)
    (hcertificateInput : RelWord.IsLemma49Input D (RelWord.symmetrized v)
      eps (1 / 1000) rho)
    (hfinalInput : RelWord.IsLemma49Input D (RelWord.symmetrized v)
      epsFinal (lemma49ScaledFinalMu powerMu divisor) rho)
    (hRel : GGT.IsQuasiGeodesicChainAt D.alphabet.carrier 4 1
      C.exteriorVertex C.contiguity.exterior.length)
    (hPow : GGT.IsQuasiGeodesicChainAt D.alphabet.carrier powerMu b
      C.powerArcVertex C.boundaryArc.length)
    (hpowerMu : 0 < powerMu) (hdivisor : 0 < divisor)
    (hdivisorMu : 32 * powerMu ≤ divisor) (hdivisorEight : 8 ≤ divisor)
    (hArcScale : divisor *
      (2 * lemma49PowerShadowError powerMu b K eps + 2) ≤
        C.boundaryArc.length)
    (hRelatorScale : 1000 * (2 * eps + 2) ≤ rho)
    (hconnectors : 2 * K ≤ epsFinal) : False := by
  let p₀ := 0
  let p₁ := B.block.length
  let p₂ := B.block.length + B.middle.length
  let p₃ := B.block.length + B.middle.length + B.block.length
  have hp₀₁ : p₀ ≤ p₁ := by dsimp [p₀, p₁]; omega
  have hp₁₂ : p₁ ≤ p₂ := by dsimp [p₁, p₂]; omega
  have hp₁₃ : p₁ ≤ p₃ := by dsimp [p₁, p₃]; omega
  have hp₂₃ : p₂ ≤ p₃ := by dsimp [p₂, p₃]; omega
  have hp₀ : p₀ ≤ C.boundaryArc.length := Nat.zero_le _
  have hp₁ : p₁ ≤ C.boundaryArc.length := B.firstEnd_le
  have hp₂ : p₂ ≤ C.boundaryArc.length := B.secondStart_le
  have hp₃ : p₃ ≤ C.boundaryArc.length := B.secondEnd_le
  have hbasicScale : divisor *
      (lemma49PowerShadowError powerMu b K eps + 1) ≤
        C.boundaryArc.length := by
    have hinside : lemma49PowerShadowError powerMu b K eps + 1 ≤
        2 * lemma49PowerShadowError powerMu b K eps + 2 := by omega
    exact le_trans (Nat.mul_le_mul_left divisor hinside) hArcScale
  have hblockFar := B.block_shadow_far hdivisor hbasicScale
  have hmiddleFar := B.middle_shadow_far hdivisorMu hdivisorEight hbasicScale
  have hj₀₁ : Sh.index p₀ < Sh.index p₁ := by
    apply Sh.index_strictMono_of_far_powerMu hpowerMu hRel hPow hp₀₁ hp₁
    dsimp [p₀, p₁]
    simpa only [Nat.zero_add, lemma49PowerShadowError] using hblockFar
  have hj₁₂ : Sh.index p₁ < Sh.index p₂ := by
    apply Sh.index_strictMono_of_far_powerMu hpowerMu hRel hPow hp₁₂ hp₂
    dsimp [p₁, p₂]
    rw [Nat.add_sub_cancel_left]
    exact hmiddleFar
  have hj₁₃ : Sh.index p₁ < Sh.index p₃ := by
    apply Sh.index_strictMono_of_far_powerMu hpowerMu hRel hPow hp₁₃ hp₃
    dsimp [p₁, p₃]
    have hgap : B.middle.length < B.middle.length + B.block.length := by
      have hblockPos : 0 < B.block.length := by
        exact lt_of_le_of_lt (Nat.zero_le _) hblockFar
      omega
    exact lt_trans hmiddleFar hgap
  have hneFar : powerMu * (2 * K + b) < B.block.length := by
    have hinside : 2 * K + b ≤ 2 * K + b + 4 * (eps + K + 1) := by omega
    have hmul := Nat.mul_le_mul_left powerMu hinside
    exact lt_of_le_of_lt hmul hblockFar
  have hj₂₃ne : Sh.index p₂ ≠ Sh.index p₃ := by
    apply Sh.index_ne_of_far_powerMu hpowerMu hPow hp₂₃ hp₃
    dsimp [p₂, p₃]
    simpa only [Nat.add_sub_cancel_left] using hneFar
  let j₀ := Sh.index p₀
  let j₁ := Sh.index p₁
  let j₂ := Sh.index p₂
  let j₃ := Sh.index p₃
  let c := min j₂ j₃
  let d := max j₂ j₃
  have hj₀₁' : j₀ < j₁ := hj₀₁
  have hj₁c : j₁ < c := by
    dsimp [c, j₁, j₂, j₃]
    rw [lt_min_iff]
    exact ⟨hj₁₂, hj₁₃⟩
  have hcd : c < d := by
    dsimp [c, d, j₂, j₃]
    exact min_lt_max.mpr hj₂₃ne
  have hdExterior : d ≤ C.contiguity.exterior.length := by
    dsimp [d, j₂, j₃]
    rw [max_le_iff]
    exact ⟨Sh.index_le p₂ hp₂, Sh.index_le p₃ hp₃⟩
  have hdRelator : d ≤ C.relator.length :=
    le_trans hdExterior C.contiguity.exterior_length_le_relator
  let first := listInterval C.relator j₀ j₁
  let middle := listInterval C.relator j₁ c
  let second := listInterval C.relator c d
  let tail := C.relator.drop d ++ C.relator.take j₀
  let rotated := C.relator.rotate j₀
  have hsplit : rotated = first ++ middle ++ second ++ tail := by
    exact rotate_eq_four_listIntervals C.relator hj₀₁'.le hj₁c.le
      hcd.le hdRelator
  have hrotatedMem : rotated ∈ RelWord.symmetrized v :=
    hfinalInput.rotate_mem C.relator C.relator_mem j₀
  have hfirstLength : first.length = j₁ - j₀ :=
    length_listInterval C.relator hj₀₁'.le
      (le_trans hj₁c.le (le_trans hcd.le hdRelator))
  have hsecondLength : second.length = d - c :=
    length_listInterval C.relator hcd.le hdRelator
  have hfirstLargeRaw := Sh.scaledRepeatedBlock_indexSpan_large B
    hcertificateInput hRel hPow hpowerMu hdivisor hArcScale hRelatorScale
    hp₀₁ hp₁ (by dsimp [p₀, p₁])
  rw [Nat.max_eq_right hj₀₁.le, Nat.min_eq_left hj₀₁.le] at hfirstLargeRaw
  have hfirstLarge : lemma49ScaledFinalMu powerMu divisor *
      (rotated.length : ℝ) ≤ (first.length : ℝ) := by
    rw [List.length_rotate, hfirstLength]
    dsimp [j₀, j₁]
    exact hfirstLargeRaw
  have hsecondLargeRaw := Sh.scaledRepeatedBlock_indexSpan_large B
    hcertificateInput hRel hPow hpowerMu hdivisor hArcScale hRelatorScale
    hp₂₃ hp₃ (by dsimp [p₂, p₃]; omega)
  have hsecondLarge : lemma49ScaledFinalMu powerMu divisor *
      (rotated.length : ℝ) ≤ (second.length : ℝ) := by
    rw [List.length_rotate, hsecondLength]
    dsimp [c, d, j₂, j₃]
    exact hsecondLargeRaw
  let e₀ := Sh.defect p₀
  let e₁ := Sh.defect p₁
  let e₂ := Sh.defect p₂
  let e₃ := Sh.defect p₃
  have he₀ : C.exteriorVertex j₀ = C.powerArcVertex p₀ * e₀ := by
    dsimp [e₀, j₀, Lemma49ContiguityShadow.defect]
    group
  have he₁ : C.exteriorVertex j₁ = C.powerArcVertex p₁ * e₁ := by
    dsimp [e₁, j₁, Lemma49ContiguityShadow.defect]
    group
  have he₂ : C.exteriorVertex j₂ = C.powerArcVertex p₂ * e₂ := by
    dsimp [e₂, j₂, Lemma49ContiguityShadow.defect]
    group
  have he₃ : C.exteriorVertex j₃ = C.powerArcVertex p₃ * e₃ := by
    dsimp [e₃, j₃, Lemma49ContiguityShadow.defect]
    group
  have hpower₀₁ := B.first_powerArc_span C
  have hpower₂₃ := B.second_powerArc_span C
  have hfirstValue : GGT.RelLetter.listVal first =
      e₀⁻¹ * GGT.RelLetter.listVal B.block * e₁ := by
    dsimp [first]
    rw [C.listVal_relatorInterval hj₀₁'.le
      (le_trans hj₁c.le (le_trans hcd.le hdExterior)), he₀, he₁]
    rw [← hpower₀₁]
    dsimp [p₀, p₁]
    group
  by_cases hforward : j₂ ≤ j₃
  · have hcEq : c = j₂ := Nat.min_eq_left hforward
    have hdEq : d = j₃ := Nat.max_eq_right hforward
    have hsecondValue : GGT.RelLetter.listVal second =
        e₂⁻¹ * GGT.RelLetter.listVal B.block * e₃ := by
      dsimp [second]
      rw [hcEq, hdEq]
      rw [C.listVal_relatorInterval hforward
        (by simpa [j₃] using Sh.index_le p₃ hp₃)]
      rw [he₂, he₃, ← hpower₂₃]
      dsimp [p₂, p₃]
      group
    let left := e₂⁻¹ * e₀
    let right := e₁⁻¹ * e₃
    have hleft : wordNorm D.alphabet.carrier left ≤ epsFinal :=
      le_trans (Sh.wordNorm_defect_inv_mul_defect_le hp₂ hp₀) hconnectors
    have hright : wordNorm D.alphabet.carrier right ≤ epsFinal :=
      le_trans (Sh.wordNorm_defect_inv_mul_defect_le hp₁ hp₃) hconnectors
    apply false_of_two_large_close_relator_subwords hfinalInput hrotatedMem
      hsplit hleft hright
    · left
      rw [hsecondValue, hfirstValue]
      dsimp [left, right]
      group
    · exact hfirstLarge
    · exact hsecondLarge
  · have hreverse : j₃ ≤ j₂ := by omega
    have hcEq : c = j₃ := Nat.min_eq_right hreverse
    have hdEq : d = j₂ := Nat.max_eq_left hreverse
    have hsecondValue : GGT.RelLetter.listVal second =
        e₃⁻¹ * (GGT.RelLetter.listVal B.block)⁻¹ * e₂ := by
      dsimp [second]
      rw [hcEq, hdEq]
      rw [C.listVal_relatorInterval hreverse
        (by simpa [j₂] using Sh.index_le p₂ hp₂)]
      rw [he₃, he₂, ← hpower₂₃]
      dsimp [p₂, p₃]
      group
    let left := e₃⁻¹ * e₁
    let right := e₀⁻¹ * e₂
    have hleft : wordNorm D.alphabet.carrier left ≤ epsFinal :=
      le_trans (Sh.wordNorm_defect_inv_mul_defect_le hp₃ hp₁) hconnectors
    have hright : wordNorm D.alphabet.carrier right ≤ epsFinal :=
      le_trans (Sh.wordNorm_defect_inv_mul_defect_le hp₀ hp₂) hconnectors
    apply false_of_two_large_close_relator_subwords hfinalInput hrotatedMem
      hsplit hleft hright
    · right
      rw [hsecondValue, hfirstValue]
      dsimp [left, right]
      group
    · exact hfirstLarge
    · exact hsecondLarge

/-! ## Model check -/

/-- The scaled coefficient is nonzero in a concrete short-power model. -/
theorem lemma49ScaledFinalMu_model :
    0 < lemma49ScaledFinalMu 7 800 := by
  exact lemma49ScaledFinalMu_pos (by omega) (by omega)

end HullSC
end GroupApproximation
