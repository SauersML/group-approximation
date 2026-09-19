import GroupApproximation.GGT.HullSCLemma49QuadrangleShadow

/-!
# Ordered shadow intervals in Hull's Lemma 4.9

Case 1 of Osin's proof of Lemma 6.3, which Hull invokes in Lemma 4.9,
chooses two equal separated subwords of the power-boundary arc and shadows
their four endpoints on the exposed relator arc.  This module proves the
parameter estimates that make the two relator intervals disjoint.

The first estimate bounds a shadow index in terms of its power-boundary
parameter.  The second says that sufficiently separated power parameters have
their shadow indices in the same order.  Both follow directly from the two
quasi-geodesic chain inequalities and the shadow distance.  The last section
checks that the large Greendlinger arc and the explicit repeated-block
decomposition satisfy the required numerical separations.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.WordMetric

universe u

/-! ## Coarse parameter control -/

/-- A shadow index cannot run far ahead of its power-boundary parameter. -/
theorem Lemma49ContiguityShadow.index_upper
    {G : Type u} [Group G] {Lambda : Type*}
    {D : GGT.RelGenSet G Lambda}
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n eps : ℕ} {mu : ℝ}
    {Z : Lemma49GeodesicPowerDiagram D v g n}
    {C : Lemma49RelativeGreendlingerCell D v g n eps mu Z} {K b : ℕ}
    (Sh : Lemma49ContiguityShadow C K)
    (hRel : GGT.IsQuasiGeodesicChainAt D.alphabet.carrier 4 1
      C.exteriorVertex C.contiguity.exterior.length)
    (hPow : GGT.IsQuasiGeodesicChainAt D.alphabet.carrier 4 b
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

/-- If two power parameters are farther apart than all endpoint and
quasi-geodesic errors, their shadow indices occur in the same order. -/
theorem Lemma49ContiguityShadow.index_strictMono_of_far
    {G : Type u} [Group G] {Lambda : Type*}
    {D : GGT.RelGenSet G Lambda}
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n eps : ℕ} {mu : ℝ}
    {Z : Lemma49GeodesicPowerDiagram D v g n}
    {C : Lemma49RelativeGreendlingerCell D v g n eps mu Z} {K b : ℕ}
    (Sh : Lemma49ContiguityShadow C K)
    (hRel : GGT.IsQuasiGeodesicChainAt D.alphabet.carrier 4 1
      C.exteriorVertex C.contiguity.exterior.length)
    (hPow : GGT.IsQuasiGeodesicChainAt D.alphabet.carrier 4 b
      C.powerArcVertex C.boundaryArc.length)
    {x y : ℕ} (hxy : x ≤ y) (hy : y ≤ C.boundaryArc.length)
    (hfar : 4 * b + 24 * K + 16 * eps + 16 * x + 16 < y - x) :
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
  have hboundReal : ((y - x : ℕ) : ℝ) ≤
      ((4 * (2 * K + Sh.index x + b) : ℕ) : ℝ) := by
    push_cast
    norm_num at hpowLower
    linarith [hdistUpperReal]
  have hbound : y - x ≤ 4 * (2 * K + Sh.index x + b) := by
    exact_mod_cast hboundReal
  have hindex := Sh.index_upper hRel hPow hx
  omega

/-- A long enough power interval cannot have coincident shadow endpoints. -/
theorem Lemma49ContiguityShadow.index_ne_of_far
    {G : Type u} [Group G] {Lambda : Type*}
    {D : GGT.RelGenSet G Lambda}
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n eps : ℕ} {mu : ℝ}
    {Z : Lemma49GeodesicPowerDiagram D v g n}
    {C : Lemma49RelativeGreendlingerCell D v g n eps mu Z} {K b : ℕ}
    (Sh : Lemma49ContiguityShadow C K)
    (hPow : GGT.IsQuasiGeodesicChainAt D.alphabet.carrier 4 b
      C.powerArcVertex C.boundaryArc.length)
    {x y : ℕ} (hxy : x ≤ y) (hy : y ≤ C.boundaryArc.length)
    (hfar : 4 * b + 8 * K < y - x) :
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
        (C.powerArcVertex x) (C.powerArcVertex y) : ℝ) ≤
        2 * (K : ℝ) := by
    exact_mod_cast hdist
  have hpowLower := (hPow x y hxy hy).1
  have hboundReal : ((y - x : ℕ) : ℝ) ≤
      ((4 * (2 * K + b) : ℕ) : ℝ) := by
    push_cast
    norm_num at hpowLower
    linarith [hdistReal]
  have hbound : y - x ≤ 4 * (2 * K + b) := by
    exact_mod_cast hboundReal
  omega

/-! ## The four repeated-block positions -/

/-- Length bookkeeping for the explicit `block middle block tail`
decomposition. -/
theorem Lemma49RepeatedBoundaryBlocks.length_eq
    {Alpha : Type*} {arc : List Alpha}
    (B : Lemma49RepeatedBoundaryBlocks Alpha arc) :
    arc.length = 2 * B.block.length + B.middle.length + B.tail.length := by
  have h := congrArg List.length B.decomposition
  simp only [List.length_append] at h
  omega

/-- The first repeated block ends on the selected arc. -/
theorem Lemma49RepeatedBoundaryBlocks.firstEnd_le
    {Alpha : Type*} {arc : List Alpha}
    (B : Lemma49RepeatedBoundaryBlocks Alpha arc) :
    B.block.length ≤ arc.length := by
  have h := B.length_eq
  omega

/-- The second repeated block starts on the selected arc. -/
theorem Lemma49RepeatedBoundaryBlocks.secondStart_le
    {Alpha : Type*} {arc : List Alpha}
    (B : Lemma49RepeatedBoundaryBlocks Alpha arc) :
    B.block.length + B.middle.length ≤ arc.length := by
  have h := B.length_eq
  omega

/-- The second repeated block ends on the selected arc. -/
theorem Lemma49RepeatedBoundaryBlocks.secondEnd_le
    {Alpha : Type*} {arc : List Alpha}
    (B : Lemma49RepeatedBoundaryBlocks Alpha arc) :
    B.block.length + B.middle.length + B.block.length ≤ arc.length := by
  have h := B.length_eq
  omega

/-! ## Scaling the selected arc -/

/-- At the Greendlinger value `mu = 1/1000`, a sufficiently large relator
makes the selected boundary arc dominate every shadowing error. -/
theorem Lemma49RelativeGreendlingerCell.boundaryArc_shadow_scale
    {G : Type u} [Group G] {Lambda : Type*}
    {D : GGT.RelGenSet G Lambda}
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n eps rho b K : ℕ}
    {Z : Lemma49GeodesicPowerDiagram D v g n}
    (C : Lemma49RelativeGreendlingerCell D v g n eps (1 / 1000) Z)
    (hinput : RelWord.IsLemma49Input D (RelWord.symmetrized v)
      eps (1 / 1000) rho)
    (hscale : 1000 * (4 * b + 24 * K + 18 * eps + 18) ≤ rho) :
    200 * (4 * b + 24 * K + 16 * eps + 17) ≤ C.boundaryArc.length := by
  have hrho := hinput.long C.relator C.relator_mem
  have hrelatorScaleNat :
      1000 * (4 * b + 24 * K + 18 * eps + 18) ≤ C.relator.length :=
    le_trans hscale hrho
  have hrelatorScale :
      (1000 : ℝ) *
          (4 * (b : ℝ) + 24 * (K : ℝ) + 18 * (eps : ℝ) + 18) ≤
        (C.relator.length : ℝ) := by
    exact_mod_cast hrelatorScaleNat
  have hexterior := C.exterior_large
  have harc := C.boundaryArc_lower hinput
  have htarget :
      (200 : ℝ) *
          (4 * (b : ℝ) + 24 * (K : ℝ) + 16 * (eps : ℝ) + 17) ≤
        (C.boundaryArc.length : ℝ) := by
    norm_num at hexterior
    linarith
  exact_mod_cast htarget

/-- The first repeated block is longer than the order-preservation error. -/
theorem Lemma49RepeatedBoundaryBlocks.block_shadow_far
    {Alpha : Type*} {arc : List Alpha}
    (B : Lemma49RepeatedBoundaryBlocks Alpha arc) {b K eps : ℕ}
    (hscale : 200 * (4 * b + 24 * K + 16 * eps + 17) ≤ arc.length) :
    4 * b + 24 * K + 16 * eps + 16 < B.block.length := by
  have hdivision := Nat.div_mul_le_self arc.length 100
  rw [B.block_length]
  omega

/-- The middle gap is long enough that the first interval precedes both
endpoints of the second interval. -/
theorem Lemma49RepeatedBoundaryBlocks.middle_shadow_far
    {Alpha : Type*} {arc : List Alpha}
    (B : Lemma49RepeatedBoundaryBlocks Alpha arc) {b K eps : ℕ}
    (hscale : 200 * (4 * b + 24 * K + 16 * eps + 17) ≤ arc.length) :
    4 * b + 24 * K + 16 * eps + 16 * B.block.length + 16 <
      B.middle.length := by
  have hdivision := Nat.div_mul_le_self arc.length 100
  have hmiddle := B.middle_long
  rw [B.block_length]
  omega

/-! ## Numerical model -/

/-- The scaling inequalities have a nonempty integral model. -/
theorem shadowScale_numericalModel :
    4 * 2 + 24 * 3 + 16 * 5 + 16 < 400 ∧
      4 * 2 + 24 * 3 + 16 * 5 + 16 * 400 + 16 < 10000 := by
  norm_num

end HullSC
end GroupApproximation
