import GroupApproximation.KunThom.CentralizerNormalizationImprove

/-!
# Repair of arrows at pair scales

The cluster groupoid on expander components uses the pair scale
`min (scale n i) (scale n l)` for arrows between objects `i` and `l`, so that
inverting an arrow keeps its threshold.  This module proves the eventual
repair statements for a `ComponentFamily` at pair scales.

`PairRepairAt K₀ h' d n` says that every arrow whose two equivariance defects
are below `K₀ * h' * min (scale n i) (scale n l) / 2` lies within
`2 * min (scale n i) (scale n l)` and within `d * |model n i|` of a cluster
candidate at threshold `h'` and the pair scale.  The finite step rounds a
relation near the swap graph of the arrow with the crossing repair of
`CentralizerNormalizationCrossingRepair` at half the threshold, and the spare
factor two absorbs the change from the source scale to the pair scale.
`PairImproveCloseAt`, the statement for composites of two candidates, follows
from `PairRepairAt` with `K₀ = 4` by subadditivity of equivariance defects.

`exists_joint_pairRepair` chooses one vanishing threshold and one vanishing
distance factor for which both statements hold eventually, with the threshold
dominating a prescribed vanishing sequence.  The module also records that an
exact directed Cheeger bound gives tagged expansion at every scale.
-/

namespace GroupApproximation
namespace CentralizerNormalizationImprove

open Filter
open scoped Topology symmDiff
open AlmostAutomorphism
open KazhdanImprovement
open FinitePartialBijection
open CentralizerNormalizationCrossingRepair
open CentralizerNormalizationSumApproximation
open CentralizerNormalizationParameters
open KunThomRounding
open KazhdanGNS

theorem nat_min_facts (a b : ℕ) :
    min a b ≤ a ∧ min a b ≤ b ∧ (min a b = a ∨ min a b = b) :=
  ⟨min_le_left a b, min_le_right a b, min_choice a b⟩

/-! ### Candidates under changes of threshold and scale -/

theorem isClusterCandidate_mono_of_le {L : Type*} [Fintype L] [DecidableEq L]
    {Y Z : FiniteModel} {actY : L → Equiv.Perm Y} {actZ : L → Equiv.Perm Z}
    {h h' : ℝ} {m m' : ℕ} {f : FinitePartialBijection Y Z}
    (hf : f.IsClusterCandidate actY actZ h m) (hh0 : 0 ≤ h) (hh : h ≤ h')
    (hm : m ≤ m') :
    f.IsClusterCandidate actY actZ h' m' := by
  have hmr : (m : ℝ) ≤ m' := by exact_mod_cast hm
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hprod : h * m ≤ h' * m' := mul_le_mul hh hmr hm0 (hh0.trans hh)
  refine ⟨?_, ?_, ?_⟩
  · have hself := hf.selfSmall
    omega
  · linarith only [hf.forwardSmall, hprod]
  · linarith only [hf.backwardSmall, hprod]

/-- A candidate at half the threshold is a candidate at every scale at least
half as large. -/
theorem isClusterCandidate_of_half_threshold {L : Type*} [Fintype L] [DecidableEq L]
    [Nonempty L] {Y Z : FiniteModel} {actY : L → Equiv.Perm Y}
    {actZ : L → Equiv.Perm Z} {h : ℝ} {m m' : ℕ} {f : FinitePartialBijection Y Z}
    (hf : f.IsClusterCandidate actY actZ (h / 2) m) (hh0 : 0 ≤ h)
    (hh : h / 2 ≤ 1 / 100000) (hm : m ≤ 2 * m') (hm' : 1 ≤ m') :
    f.IsClusterCandidate actY actZ h m' := by
  obtain ⟨hs, ht⟩ := hundred_mul_defects_le_of_candidate hf hh
  have hmr : (m : ℝ) ≤ 2 * (m' : ℝ) := by exact_mod_cast hm
  have hprod : h / 2 * m ≤ h / 2 * (2 * (m' : ℝ)) :=
    mul_le_mul_of_nonneg_left hmr (by linarith only [hh0])
  refine ⟨?_, ?_, ?_⟩
  · omega
  · linarith only [hf.forwardSmall, hprod]
  · linarith only [hf.backwardSmall, hprod]

/-! ### Tagged expansion from directed Cheeger bounds -/

theorem card_directedBoundary_le_card_taggedBoundary {K : Type} {T : Finset K}
    {Y : FiniteModel} (act : K → Equiv.Perm Y) (A : Finset Y) :
    (directedBoundary Y (T.image act) A).card ≤
      (taggedBoundary (fun t : T ↦ act t.1) A).card := by
  classical
  refine (Finset.card_le_card ?_).trans
    (Finset.card_image_le (s := taggedBoundary (fun t : T ↦ act t.1) A)
      (f := fun p : T × Y ↦ ((act p.1.1, p.2) : Arc Y)))
  intro p hp
  rw [mem_directedBoundary] at hp
  obtain ⟨hσ, hcross⟩ := hp
  obtain ⟨k, hk, hkσ⟩ := Finset.mem_image.mp hσ
  refine Finset.mem_image.mpr ⟨(⟨k, hk⟩, p.2), ?_, ?_⟩
  · simpa only [mem_taggedBoundary, hkσ] using hcross
  · exact Prod.ext hkσ rfl

/-- An exact directed Cheeger bound for the image labels gives tagged expansion
at every scale for every smaller positive constant. -/
theorem hasTaggedExpansionAtScale_of_cheeger {K : Type} {T : Finset K}
    {Y : FiniteModel} {act : K → Equiv.Perm Y} {c h : ℝ}
    (hc : DirectedCoarea.HasCheegerLowerBound Y (T.image act) c) (hh : 0 < h)
    (hhc : h ≤ c) (m : ℕ) :
    HasTaggedExpansionAtScale (fun t : T ↦ act t.1) h m := by
  refine ⟨hh, fun A _ hA ↦ ?_⟩
  rcases A.eq_empty_or_nonempty with hempty | hne
  · subst hempty
    simp
  · have h1 := hc.2 A hne hA
    have h2 : ((directedBoundary Y (T.image act) A).card : ℝ) ≤
        ((taggedBoundary (fun t : T ↦ act t.1) A).card : ℝ) := by
      exact_mod_cast card_directedBoundary_le_card_taggedBoundary act A
    have h3 : h * (A.card : ℝ) ≤ c * A.card :=
      mul_le_mul_of_nonneg_right hhc (by positivity)
    linarith only [h1, h2, h3]

/-! ### Swap encodings of single arrows -/

theorem card_badArcs_swap_le {L : Type*} [Fintype L] [DecidableEq L]
    {X Z : FiniteModel} (actX : L → Equiv.Perm X) (actZ : L → Equiv.Perm Z)
    (b : FinitePartialBijection X Z) :
    (badArcs (sumModel X Z) (Finset.univ.image (sumAction actX actZ)) b.swapPerm).card ≤
      (b.equivarianceDefect actX actZ).card + (b.symm.equivarianceDefect actZ actX).card :=
  (card_badArcs_image_sumAction_le actX actZ b.swapPerm).trans
    (card_swapEquivarianceDefect_le b actX actZ)

theorem card_badArcs_swap_inv_le {L : Type*} [Fintype L] [DecidableEq L]
    {X Z : FiniteModel} (actX : L → Equiv.Perm X) (actZ : L → Equiv.Perm Z)
    (b : FinitePartialBijection X Z) :
    (badArcs (sumModel X Z) (Finset.univ.image (sumAction actX actZ))
        b.swapPerm⁻¹).card ≤
      (b.equivarianceDefect actX actZ).card + (b.symm.equivarianceDefect actZ actX).card := by
  rw [card_badArcs_inv]
  exact card_badArcs_swap_le actX actZ b

/-! ### Real arithmetic, stated over plain variables -/

theorem arith_forward_half {c s SW B p η W mX : ℝ} (hc : 0 < c) (hs : 1 ≤ s)
    (hSW : SW ≤ s) (hB0 : 0 ≤ B) (hB : B < p * η * W) (hpη : 0 ≤ p * η)
    (hW : W ≤ 90 * mX) (hid : (2 + c) * s * (c + 7 * s) * p = c ^ 2 / 360) :
    (2 * s + c * s) * ((c + 7 * SW) * B) < c * c * (η / 2 * mX / 2) := by
  have hcoef : 0 < 2 * s + c * s := by nlinarith only [hc, hs]
  have hc7 : 0 < c + 7 * s := by linarith only [hc, hs]
  have step1 : (2 * s + c * s) * ((c + 7 * SW) * B) ≤
      (2 * s + c * s) * ((c + 7 * s) * B) := by
    refine mul_le_mul_of_nonneg_left ?_ hcoef.le
    refine mul_le_mul_of_nonneg_right ?_ hB0
    linarith only [hSW]
  have step2 : (2 * s + c * s) * ((c + 7 * s) * B) <
      (2 * s + c * s) * ((c + 7 * s) * (p * η * W)) :=
    mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left hB hc7) hcoef
  have step3 : (2 * s + c * s) * ((c + 7 * s) * (p * η * W)) ≤
      (2 * s + c * s) * ((c + 7 * s) * (p * η * (90 * mX))) := by
    refine mul_le_mul_of_nonneg_left ?_ hcoef.le
    refine mul_le_mul_of_nonneg_left ?_ hc7.le
    exact mul_le_mul_of_nonneg_left hW hpη
  have step4 : (2 * s + c * s) * ((c + 7 * s) * (p * η * (90 * mX))) =
      90 * η * mX * ((2 + c) * s * (c + 7 * s) * p) := by ring
  rw [hid] at step4
  have step5 : 90 * η * mX * (c ^ 2 / 360) = c * c * (η / 2 * mX / 2) := by ring
  linarith only [step1, step2, step3, step4, step5]

theorem arith_defects_lt {sT sd td a b κ m mX ζ : ℝ} (hsT : 1 ≤ sT)
    (hsd : sT * sd ≤ a) (htd : sT * td ≤ b) (ha : a < κ * m / 2)
    (hb : b < κ * m / 2) (hsd0 : 0 ≤ sd) (htd0 : 0 ≤ td) (hm : m ≤ mX)
    (hκ0 : 0 ≤ κ) (hκζ : κ < ζ) (hmX : 0 < mX) : sd + td < ζ * mX := by
  have h1 : sd ≤ sT * sd := by nlinarith only [hsT, hsd0]
  have h2 : td ≤ sT * td := by nlinarith only [hsT, htd0]
  have h3 : κ * m ≤ κ * mX := mul_le_mul_of_nonneg_left hm hκ0
  have h4 : κ * mX < ζ * mX := mul_lt_mul_of_pos_right hκζ hmX
  linarith only [hsd, htd, ha, hb, h1, h2, h3, h4]

theorem arith_distance_repair {D dsum E ζ mX : ℝ} (hD : D ≤ dsum + 6 * E)
    (hdsum : dsum < ζ * mX) (hE : E < 3240 * ζ * mX) (hmX : 0 ≤ mX) (hζ : 0 ≤ ζ) :
    D ≤ 20000 * ζ * mX := by
  have h0 : 0 ≤ ζ * mX := mul_nonneg hζ hmX
  linarith only [hD, hdsum, hE, h0]

theorem arith_lt_scale {D ζ mX : ℝ} (hD : D ≤ 20000 * ζ * mX) (hζ : ζ ≤ 1 / 100000)
    (hmX : 1 ≤ mX) : D < mX := by
  have h1 : ζ * mX ≤ 1 / 100000 * mX :=
    mul_le_mul_of_nonneg_right hζ (by linarith only [hmX])
  linarith only [hD, h1, hmX]

theorem arith_scale_card {D ζ mX X : ℝ} (hD : D ≤ 20000 * ζ * mX) (hX : mX ≤ X)
    (hζ : 0 ≤ ζ) : D ≤ 20000 * ζ * X := by
  have h1 : 20000 * ζ * mX ≤ 20000 * ζ * X :=
    mul_le_mul_of_nonneg_left hX (by linarith only [hζ])
  linarith only [hD, h1]

/-! ### Repair and improvement at pair scales -/

namespace ComponentFamily

variable {K : Type} [Group K] {T : Finset K} (F : ComponentFamily K T)

open Classical in
/-- Repair of single arrows at index `n`, threshold `h'` and distance factor
`d`: an arrow whose equivariance defects are below the pair threshold times
`K₀` is close to a candidate at the pair scale. -/
def PairRepairAt (K₀ h' d : ℝ) (n : ℕ) : Prop :=
  ∀ (i l : F.index n) (b : FinitePartialBijection (F.model n i) (F.model n l)),
    ((b.equivarianceDefect (F.tags n i) (F.tags n l)).card : ℝ) <
      K₀ * h' * ((min (F.scale n i) (F.scale n l) : ℕ) : ℝ) / 2 →
    ((b.symm.equivarianceDefect (F.tags n l) (F.tags n i)).card : ℝ) <
      K₀ * h' * ((min (F.scale n i) (F.scale n l) : ℕ) : ℝ) / 2 →
    ∃ r : FinitePartialBijection (F.model n i) (F.model n l),
      r.IsClusterCandidate (F.tags n i) (F.tags n l) h'
          (min (F.scale n i) (F.scale n l)) ∧
        r.twoSidedDisagreement b < 2 * min (F.scale n i) (F.scale n l) ∧
        (r.twoSidedDisagreement b : ℝ) ≤ d * Fintype.card (F.model n i)

open Classical in
/-- Improvement of composites at index `n`, with candidates at pair scales. -/
def PairImproveCloseAt (h' d : ℝ) (n : ℕ) : Prop :=
  ∀ (i j l : F.index n)
    (f : FinitePartialBijection (F.model n i) (F.model n j)),
    f.IsClusterCandidate (F.tags n i) (F.tags n j) h'
      (min (F.scale n i) (F.scale n j)) →
    ∀ g : FinitePartialBijection (F.model n j) (F.model n l),
    g.IsClusterCandidate (F.tags n j) (F.tags n l) h'
      (min (F.scale n j) (F.scale n l)) →
    ∃ r : FinitePartialBijection (F.model n i) (F.model n l),
      r.IsClusterCandidate (F.tags n i) (F.tags n l) h'
          (min (F.scale n i) (F.scale n l)) ∧
        r.twoSidedDisagreement (f.trans g) < 2 * min (F.scale n i) (F.scale n l) ∧
        (r.twoSidedDisagreement (f.trans g) : ℝ) ≤ d * Fintype.card (F.model n i)

open Classical in
/-- A counterexample to repair at index `n`. -/
structure BadArrow (K₀ h' d : ℝ) (n : ℕ) where
  i : F.index n
  l : F.index n
  b : FinitePartialBijection (F.model n i) (F.model n l)
  forward : ((b.equivarianceDefect (F.tags n i) (F.tags n l)).card : ℝ) <
    K₀ * h' * ((min (F.scale n i) (F.scale n l) : ℕ) : ℝ) / 2
  backward : ((b.symm.equivarianceDefect (F.tags n l) (F.tags n i)).card : ℝ) <
    K₀ * h' * ((min (F.scale n i) (F.scale n l) : ℕ) : ℝ) / 2
  noRepair : ∀ r : FinitePartialBijection (F.model n i) (F.model n l),
    ¬ (r.IsClusterCandidate (F.tags n i) (F.tags n l) h'
          (min (F.scale n i) (F.scale n l)) ∧
      r.twoSidedDisagreement b < 2 * min (F.scale n i) (F.scale n l) ∧
      (r.twoSidedDisagreement b : ℝ) ≤ d * Fintype.card (F.model n i))

theorem pairRepairAt_of_not_nonempty {K₀ h' d : ℝ} {n : ℕ}
    (h : ¬ Nonempty (F.BadArrow K₀ h' d n)) : F.PairRepairAt K₀ h' d n := by
  classical
  intro i l b hforward hbackward
  by_contra hno
  exact h ⟨⟨i, l, b, hforward, hbackward, fun r hr ↦ hno ⟨r, hr⟩⟩⟩

namespace BadArrow

variable {F}

open Classical in
/-- Natural-number size facts for a counterexample to repair. -/
theorem sizes {K₀ h' d : ℝ} {n : ℕ} (B : F.BadArrow K₀ h' d n)
    (hK0 : 0 ≤ K₀ * h') (hK : K₀ * h' ≤ 1 / 100000) (hone : (1 : K) ∈ T) :
    1 ≤ min (F.scale n B.i) (F.scale n B.l) ∧
      100 * B.b.sourceDefect ≤ min (F.scale n B.i) (F.scale n B.l) ∧
      100 * B.b.targetDefect ≤ min (F.scale n B.i) (F.scale n B.l) ∧
      18 * F.scale n B.i ≤ Fintype.card (F.model n B.i) ∧
      Fintype.card (F.model n B.i) + Fintype.card (F.model n B.l) ≤ 90 * F.scale n B.i ∧
      17 * F.scale n B.i ≤ Fintype.card (F.model n B.l) ∧
      F.scale n B.i ≤ 2 * min (F.scale n B.i) (F.scale n B.l) := by
  have hsT : (1 : ℝ) ≤ Fintype.card T := by
    rw [Fintype.card_coe]
    exact_mod_cast Finset.card_pos.mpr ⟨(1 : K), hone⟩
  have hm0 : (0 : ℝ) ≤ ((min (F.scale n B.i) (F.scale n B.l) : ℕ) : ℝ) := by positivity
  have hsdR : (Fintype.card T : ℝ) * B.b.sourceDefect ≤
      ((B.b.equivarianceDefect (F.tags n B.i) (F.tags n B.l)).card : ℝ) := by
    exact_mod_cast card_mul_sourceDefect_le_card_equivarianceDefect B.b
      (F.tags n B.i) (F.tags n B.l)
  have htdR : (Fintype.card T : ℝ) * B.b.targetDefect ≤
      ((B.b.symm.equivarianceDefect (F.tags n B.l) (F.tags n B.i)).card : ℝ) := by
    exact_mod_cast card_mul_targetDefect_le_card_symm_equivarianceDefect B.b
      (F.tags n B.i) (F.tags n B.l)
  have hsd0 : (0 : ℝ) ≤ B.b.sourceDefect := by positivity
  have htd0 : (0 : ℝ) ≤ B.b.targetDefect := by positivity
  have hprod : K₀ * h' * ((min (F.scale n B.i) (F.scale n B.l) : ℕ) : ℝ) ≤
      1 / 100000 * ((min (F.scale n B.i) (F.scale n B.l) : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_right hK hm0
  have hsdle : (B.b.sourceDefect : ℝ) ≤ Fintype.card T * B.b.sourceDefect := by
    nlinarith only [hsT, hsd0]
  have htdle : (B.b.targetDefect : ℝ) ≤ Fintype.card T * B.b.targetDefect := by
    nlinarith only [hsT, htd0]
  have hsd100 : 100 * B.b.sourceDefect ≤ min (F.scale n B.i) (F.scale n B.l) := by
    have hreal : (100 * B.b.sourceDefect : ℝ) ≤
        ((min (F.scale n B.i) (F.scale n B.l) : ℕ) : ℝ) := by
      linarith only [hsdR, B.forward, hprod, hsdle, hm0]
    exact_mod_cast hreal
  have htd100 : 100 * B.b.targetDefect ≤ min (F.scale n B.i) (F.scale n B.l) := by
    have hreal : (100 * B.b.targetDefect : ℝ) ≤
        ((min (F.scale n B.i) (F.scale n B.l) : ℕ) : ℝ) := by
      linarith only [htdR, B.backward, hprod, htdle, hm0]
    exact_mod_cast hreal
  obtain ⟨hmin1, hmin2, hmin3⟩ := nat_min_facts (F.scale n B.i) (F.scale n B.l)
  have hm1 : 1 ≤ min (F.scale n B.i) (F.scale n B.l) := by
    by_contra hlt
    have hzero : min (F.scale n B.i) (F.scale n B.l) = 0 := by omega
    have hf := B.forward
    simp only [hzero, Nat.cast_zero, mul_zero, zero_div] at hf
    have hpos : (0 : ℝ) ≤
        ((B.b.equivarianceDefect (F.tags n B.i) (F.tags n B.l)).card : ℝ) := by
      positivity
    linarith only [hf, hpos]
  have hX1 := card_source_le_card_target_add B.b
  have hZ1 := card_target_le_card_source_add B.b
  have hsi : F.scale n B.i = Fintype.card (F.model n B.i) / 18 := rfl
  have hsl : F.scale n B.l = Fintype.card (F.model n B.l) / 18 := rfl
  refine ⟨hm1, hsd100, htd100, ?_⟩
  omega

open Classical in
/-- The swap encoding of a counterexample is good for the union labels at the
goodness `K₀ * η`. -/
theorem swap_isEpsilonGood {K₀ η d : ℝ} {n : ℕ} (B : F.BadArrow K₀ η d n)
    (hK0 : 0 ≤ K₀ * η) (hK : K₀ * η ≤ 1 / 100000) (hone : (1 : K) ∈ T) :
    IsEpsilonGood (sumModel (F.model n B.i) (F.model n B.l))
      (Finset.univ.image (sumAction (F.tags n B.i) (F.tags n B.l))) (K₀ * η)
      B.b.swapPerm := by
  obtain ⟨_, _, _, h18, _, _, _⟩ := B.sizes hK0 hK hone
  obtain ⟨hmin1, _, _⟩ := nat_min_facts (F.scale n B.i) (F.scale n B.l)
  have hsum : Fintype.card (sumModel (F.model n B.i) (F.model n B.l)) =
      Fintype.card (F.model n B.i) + Fintype.card (F.model n B.l) := Fintype.card_sum
  have hmWnat : min (F.scale n B.i) (F.scale n B.l) ≤
      Fintype.card (sumModel (F.model n B.i) (F.model n B.l)) := by
    rw [hsum]
    omega
  have hmW : ((min (F.scale n B.i) (F.scale n B.l) : ℕ) : ℝ) ≤
      (Fintype.card (sumModel (F.model n B.i) (F.model n B.l)) : ℝ) := by
    exact_mod_cast hmWnat
  have hprod : K₀ * η * ((min (F.scale n B.i) (F.scale n B.l) : ℕ) : ℝ) ≤
      K₀ * η * (Fintype.card (sumModel (F.model n B.i) (F.model n B.l)) : ℝ) :=
    mul_le_mul_of_nonneg_left hmW hK0
  refine ⟨?_, ?_⟩
  · have hc :
        ((badArcs (sumModel (F.model n B.i) (F.model n B.l))
          (Finset.univ.image (sumAction (F.tags n B.i) (F.tags n B.l)))
          B.b.swapPerm).card : ℝ) ≤
        ((B.b.equivarianceDefect (F.tags n B.i) (F.tags n B.l)).card : ℝ) +
          ((B.b.symm.equivarianceDefect (F.tags n B.l) (F.tags n B.i)).card : ℝ) := by
      exact_mod_cast card_badArcs_swap_le (F.tags n B.i) (F.tags n B.l) B.b
    linarith only [hc, B.forward, B.backward, hprod]
  · have hc :
        ((badArcs (sumModel (F.model n B.i) (F.model n B.l))
          (Finset.univ.image (sumAction (F.tags n B.i) (F.tags n B.l)))
          B.b.swapPerm⁻¹).card : ℝ) ≤
        ((B.b.equivarianceDefect (F.tags n B.i) (F.tags n B.l)).card : ℝ) +
          ((B.b.symm.equivarianceDefect (F.tags n B.l) (F.tags n B.i)).card : ℝ) := by
      exact_mod_cast card_badArcs_swap_inv_le (F.tags n B.i) (F.tags n B.l) B.b
    linarith only [hc, B.forward, B.backward, hprod]

open Classical in
/-- **A relation near the swap graph with small boundary contradicts a
counterexample to repair.** -/
theorem exists_repair {K₀ η ζ : ℝ} {k n : ℕ} (B : F.BadArrow K₀ η (20000 * ζ) n)
    (hone : (1 : K) ∈ T) (hK₀ : 1 ≤ K₀) (hη : 0 < η) (hζ : ζ ≤ 1 / 100000)
    (hηζ : K₀ * η < ζ) (hkη : (k : ℝ) ^ 2 * (K₀ * η) < ζ)
    (U : Finset (sumModel (F.model n B.i) (F.model n B.l) ×
      sumModel (F.model n B.i) (F.model n B.l)))
    (hUclose : ((U ∆ permutationGraph (sumModel (F.model n B.i) (F.model n B.l))
        B.b.swapPerm).card : ℝ) <
      36 * (k : ℝ) ^ 2 * (T.card : ℝ)⁻¹ * (K₀ * η) *
        (Fintype.card (sumModel (F.model n B.i) (F.model n B.l)) : ℝ))
    (hUboundary : ((relationBoundary (sumModel (F.model n B.i) (F.model n B.l))
        (Finset.univ.image (sumAction (F.tags n B.i) (F.tags n B.l))) U).card : ℝ) <
      F.repairFactor * η *
        (Fintype.card (sumModel (F.model n B.i) (F.model n B.l)) : ℝ)) :
    False := by
  haveI : Nonempty T := ⟨⟨1, hone⟩⟩
  have hK0 : 0 ≤ K₀ * η := mul_nonneg (by linarith only [hK₀]) hη.le
  have hK : K₀ * η ≤ 1 / 100000 := by linarith only [hηζ, hζ]
  obtain ⟨hm1, hsd100, htd100, h18, h90, h17, hXm⟩ := B.sizes hK0 hK hone
  obtain ⟨hmin1, hmin2, hmin3⟩ := nat_min_facts (F.scale n B.i) (F.scale n B.l)
  have hc := F.cheeger_pos
  have hTc : (1 : ℝ) ≤ T.card := by exact_mod_cast Finset.card_pos.mpr ⟨(1 : K), hone⟩
  have hsT : (1 : ℝ) ≤ Fintype.card T := by rw [Fintype.card_coe]; exact hTc
  have hζ0 : 0 ≤ ζ := by linarith only [hηζ, hK0]
  have hsum : Fintype.card (sumModel (F.model n B.i) (F.model n B.l)) =
      Fintype.card (F.model n B.i) + Fintype.card (F.model n B.l) := Fintype.card_sum
  have hWle : Fintype.card (sumModel (F.model n B.i) (F.model n B.l)) ≤
      90 * F.scale n B.i := by
    rw [hsum]
    exact h90
  have hWr : (Fintype.card (sumModel (F.model n B.i) (F.model n B.l)) : ℝ) ≤
      90 * (F.scale n B.i : ℝ) := by exact_mod_cast hWle
  have hW0 : (0 : ℝ) ≤ (Fintype.card (sumModel (F.model n B.i) (F.model n B.l)) : ℝ) := by
    positivity
  have hX1 : 1 ≤ F.scale n B.i := by omega
  have hmX1 : (1 : ℝ) ≤ F.scale n B.i := by exact_mod_cast hX1
  -- The edit count.
  have hE := arith_edits hUclose hTc hkη hWr hW0 (by positivity) hK0 hζ0
  have hE100 : 100 * (U ∆ permutationGraph (sumModel (F.model n B.i) (F.model n B.l))
      B.b.swapPerm).card < 4 * F.scale n B.i := by
    have hreal := arith_hundred_edits hE hζ hmX1
    exact_mod_cast hreal
  have hEdits :
      (permutationGraph (sumModel (F.model n B.i) (F.model n B.l)) B.b.swapPerm \ U).card +
        (U \ permutationGraph (sumModel (F.model n B.i) (F.model n B.l))
          B.b.swapPerm).card ≤
      (U ∆ permutationGraph (sumModel (F.model n B.i) (F.model n B.l))
          B.b.swapPerm).card :=
    le_of_eq (card_sdiff_add_card_sdiff_eq_symmDiff U
      (permutationGraph (sumModel (F.model n B.i) (F.model n B.l)) B.b.swapPerm))
  have hsmallX :
      2 * (B.b.sourceDefect +
        3 * (U ∆ permutationGraph (sumModel (F.model n B.i) (F.model n B.l))
          B.b.swapPerm).card) ≤ Fintype.card (F.model n B.i) := by
    omega
  have hsmallZ :
      2 * (B.b.targetDefect +
        3 * (U ∆ permutationGraph (sumModel (F.model n B.i) (F.model n B.l))
          B.b.swapPerm).card) ≤ Fintype.card (F.model n B.l) := by
    omega
  have hclose :
      B.b.sourceDefect + B.b.targetDefect +
          6 * (U ∆ permutationGraph (sumModel (F.model n B.i) (F.model n B.l))
            B.b.swapPerm).card < 2 * F.scale n B.i := by
    omega
  -- The boundary inequality at half the threshold.
  have hSWnat : (Finset.univ.image (sumAction (F.tags n B.i) (F.tags n B.l))).card ≤
      T.card :=
    Finset.card_image_le.trans (Finset.card_univ.trans (Fintype.card_coe T)).le
  have hSW : ((Finset.univ.image (sumAction (F.tags n B.i) (F.tags n B.l))).card : ℝ) ≤
      T.card := by exact_mod_cast hSWnat
  have hB0 : (0 : ℝ) ≤ ((relationBoundary (sumModel (F.model n B.i) (F.model n B.l))
      (Finset.univ.image (sumAction (F.tags n B.i) (F.tags n B.l))) U).card : ℝ) := by
    positivity
  have hpη : 0 ≤ F.repairFactor * η := (mul_pos (F.repairFactor_pos hone) hη).le
  have hforwardT := arith_forward_half hc hTc hSW hB0 hUboundary hpη hWr
    (F.repairFactor_identity hone)
  have hforward :
      (2 * (Fintype.card T : ℝ) + F.cheeger * Fintype.card T) *
          ((F.cheeger + 7 * (Finset.univ.image
              (sumAction (F.tags n B.i) (F.tags n B.l))).card) *
            ((relationBoundary (sumModel (F.model n B.i) (F.model n B.l))
              (Finset.univ.image (sumAction (F.tags n B.i) (F.tags n B.l))) U).card : ℝ)) <
        F.cheeger * F.cheeger * (η / 2 * F.scale n B.i / 2) := by
    rw [Fintype.card_coe]
    exact hforwardT
  have hXcheeger : DirectedCoarea.HasCheegerLowerBound (F.model n B.i)
      (Finset.univ.image (F.tags n B.i)) F.cheeger := by
    rw [F.univ_image_tags]
    exact F.expands n B.i
  have hZcheeger : DirectedCoarea.HasCheegerLowerBound (F.model n B.l)
      (Finset.univ.image (F.tags n B.l)) F.cheeger := by
    rw [F.univ_image_tags]
    exact F.expands n B.l
  have hrep := repairRelation_extractCrossing_candidate_and_close
    (F.tags n B.i) (F.tags n B.l) hXcheeger hZcheeger B.b U _ hEdits
    hsmallX hsmallZ hclose hforward
  -- The distance bound.
  have hham :
      (hammingDisagreement B.b.swapPerm
        (repairRelation (sumModel (F.model n B.i) (F.model n B.l)) U)).card ≤
      3 * (U ∆ permutationGraph (sumModel (F.model n B.i) (F.model n B.l))
          B.b.swapPerm).card := by
    have h := card_repairRelation_disagreement_le
      (sumModel (F.model n B.i) (F.model n B.l)) U B.b.swapPerm
    rw [card_hammingDisagreement_comm]
    omega
  have hhamInv :
      (hammingDisagreement B.b.swapPerm⁻¹
        (repairRelation (sumModel (F.model n B.i) (F.model n B.l)) U)⁻¹).card ≤
      3 * (U ∆ permutationGraph (sumModel (F.model n B.i) (F.model n B.l))
          B.b.swapPerm).card := by
    rw [card_hammingDisagreement_inv]
    exact hham
  have hdist := twoSidedDisagreement_extractCrossing_le B.b
    (repairRelation (sumModel (F.model n B.i) (F.model n B.l)) U)
  have hdistNat :
      B.b.twoSidedDisagreement
          (extractCrossing (repairRelation (sumModel (F.model n B.i) (F.model n B.l)) U)) ≤
        (B.b.sourceDefect + B.b.targetDefect) +
          6 * (U ∆ permutationGraph (sumModel (F.model n B.i) (F.model n B.l))
            B.b.swapPerm).card := by
    omega
  have hdistReal :
      ((B.b.twoSidedDisagreement
          (extractCrossing (repairRelation (sumModel (F.model n B.i) (F.model n B.l)) U)) :
            ℕ) : ℝ) ≤
        ((B.b.sourceDefect + B.b.targetDefect : ℕ) : ℝ) +
          6 * ((U ∆ permutationGraph (sumModel (F.model n B.i) (F.model n B.l))
            B.b.swapPerm).card : ℝ) := by
    exact_mod_cast hdistNat
  have hsdR : (Fintype.card T : ℝ) * B.b.sourceDefect ≤
      ((B.b.equivarianceDefect (F.tags n B.i) (F.tags n B.l)).card : ℝ) := by
    exact_mod_cast card_mul_sourceDefect_le_card_equivarianceDefect B.b
      (F.tags n B.i) (F.tags n B.l)
  have htdR : (Fintype.card T : ℝ) * B.b.targetDefect ≤
      ((B.b.symm.equivarianceDefect (F.tags n B.l) (F.tags n B.i)).card : ℝ) := by
    exact_mod_cast card_mul_targetDefect_le_card_symm_equivarianceDefect B.b
      (F.tags n B.i) (F.tags n B.l)
  have hmleX : ((min (F.scale n B.i) (F.scale n B.l) : ℕ) : ℝ) ≤ (F.scale n B.i : ℝ) := by
    exact_mod_cast hmin1
  have hdsum : ((B.b.sourceDefect + B.b.targetDefect : ℕ) : ℝ) < ζ * F.scale n B.i := by
    push_cast
    exact arith_defects_lt hsT hsdR htdR B.forward B.backward (by positivity)
      (by positivity) hmleX hK0 hηζ (by linarith only [hmX1])
  have hfinal := arith_distance_repair hdistReal hdsum hE (by positivity) hζ0
  -- The candidate at the pair scale.
  have hηle : η ≤ K₀ * η := le_mul_of_one_le_left hη.le hK₀
  have hr' : (extractCrossing (repairRelation (sumModel (F.model n B.i) (F.model n B.l))
      U)).IsClusterCandidate (F.tags n B.i) (F.tags n B.l) η
        (min (F.scale n B.i) (F.scale n B.l)) :=
    isClusterCandidate_of_half_threshold hrep.1 hη.le (by linarith only [hK, hηle])
      hXm hm1
  have hlt : ((B.b.twoSidedDisagreement
      (extractCrossing (repairRelation (sumModel (F.model n B.i) (F.model n B.l)) U)) :
        ℕ) : ℝ) < (F.scale n B.i : ℝ) := arith_lt_scale hfinal hζ hmX1
  have hltNat : B.b.twoSidedDisagreement
      (extractCrossing (repairRelation (sumModel (F.model n B.i) (F.model n B.l)) U)) <
      F.scale n B.i := by exact_mod_cast hlt
  have hmXle : (F.scale n B.i : ℝ) ≤ (Fintype.card (F.model n B.i) : ℝ) := by
    have h : F.scale n B.i ≤ Fintype.card (F.model n B.i) := by omega
    exact_mod_cast h
  have hcard := arith_scale_card hfinal hmXle hζ0
  refine B.noRepair
    (extractCrossing (repairRelation (sumModel (F.model n B.i) (F.model n B.l)) U))
    ⟨hr', ?_, ?_⟩
  · rw [twoSidedDisagreement_comm]
    omega
  · rw [twoSidedDisagreement_comm]
    exact hcard

end BadArrow

open Classical in
/-- **Repair at fixed parameters.** -/
theorem eventually_pairRepairAt
    {Q : Finset K} {κ : ℝ} (hQ : IsKazhdanPair.{0, 0} K Q κ) (hQT : Q ⊆ T)
    (hone : (1 : K) ∈ T) (hκone : κ ≤ 1) {K₀ : ℝ} (hK₀ : 1 ≤ K₀)
    {k : ℕ} {η δ ζ : ℝ} (hk : 0 < k) (hη : 0 < η) (hδ : 0 < δ)
    (hζ : ζ ≤ 1 / 100000) (hηζ : K₀ * η < ζ) (hkη : (k : ℝ) ^ 2 * (K₀ * η) < ζ)
    (hnumerical : 16 * (T.card : ℝ) ^ 4 *
        (16 * (1 - κ ^ 2 / (4 * T.card)) ^ (2 * k) * (T.card : ℝ)⁻¹ * (K₀ * η) + δ) <
      (((1 : ℝ) / 3) * (((2 : ℝ) / 3) - (1 : ℝ) / 3) ^ 2) ^ 2 *
        (F.repairFactor * η) ^ 4) :
    ∃ N : ℕ, ∀ n ≥ N, F.PairRepairAt K₀ η (20000 * ζ) n := by
  classical
  by_contra hcontra
  have hbad : ∀ N : ℕ, ∃ n, N ≤ n ∧ Nonempty (F.BadArrow K₀ η (20000 * ζ) n) := by
    intro N
    by_contra hN
    exact hcontra ⟨N, fun n hn ↦
      F.pairRepairAt_of_not_nonempty fun hne ↦ hN ⟨n, hn, hne⟩⟩
  choose seq hseq hbadN using hbad
  have hK0 : 0 ≤ K₀ * η := mul_nonneg (by linarith only [hK₀]) hη.le
  have hKpos : 0 < K₀ * η := mul_pos (by linarith only [hK₀]) hη
  have hK : K₀ * η ≤ 1 / 100000 := by linarith only [hηζ, hζ]
  let bad : ∀ N, F.BadArrow K₀ η (20000 * ζ) (seq N) := fun N ↦ Classical.choice (hbadN N)
  let modelX : ℕ → FiniteModel := fun N ↦ F.model (seq N) (bad N).i
  let modelZ : ℕ → FiniteModel := fun N ↦ F.model (seq N) (bad N).l
  let actX : ∀ N, K → Equiv.Perm (modelX N) := fun N ↦ F.act (seq N) (bad N).i
  let actZ : ∀ N, K → Equiv.Perm (modelZ N) := fun N ↦ F.act (seq N) (bad N).l
  have hposX : ∀ N, 0 < Fintype.card (modelX N) := by
    intro N
    obtain ⟨hm1, _, _, h18, _, _, _⟩ := (bad N).sizes hK0 hK hone
    obtain ⟨hmin1, _, _⟩ := nat_min_facts (F.scale (seq N) (bad N).i)
      (F.scale (seq N) (bad N).l)
    show 0 < Fintype.card (F.model (seq N) (bad N).i)
    omega
  have hposZ : ∀ N, 0 < Fintype.card (modelZ N) := by
    intro N
    obtain ⟨hm1, _, _, _, _, h17, _⟩ := (bad N).sizes hK0 hK hone
    obtain ⟨hmin1, _, _⟩ := nat_min_facts (F.scale (seq N) (bad N).i)
      (F.scale (seq N) (bad N).l)
    show 0 < Fintype.card (F.model (seq N) (bad N).l)
    omega
  have hcard : ∀ M : ℕ, ∃ N₀ : ℕ, ∀ N ≥ N₀, M ≤ Fintype.card (modelX N) := by
    intro M
    obtain ⟨N₀, hN₀⟩ := F.size_tendsTo M
    exact ⟨N₀, fun N hN ↦ hN₀ (seq N) (hN.trans (hseq N)) (bad N).i⟩
  have hmulX : ∀ (g h : K) (ε : ℝ), 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀,
      hammingDistance (modelX N) (actX N (g * h)) (actX N g * actX N h) < ε := by
    intro g h ε hε
    obtain ⟨N₀, hN₀⟩ := F.locallyMultiplicative g h ε hε
    exact ⟨N₀, fun N hN ↦ hN₀ (seq N) (hN.trans (hseq N)) (bad N).i⟩
  have hmulZ : ∀ (g h : K) (ε : ℝ), 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀,
      hammingDistance (modelZ N) (actZ N (g * h)) (actZ N g * actZ N h) < ε := by
    intro g h ε hε
    obtain ⟨N₀, hN₀⟩ := F.locallyMultiplicative g h ε hε
    exact ⟨N₀, fun N hN ↦ hN₀ (seq N) (hN.trans (hseq N)) (bad N).l⟩
  let A := sumApproximation modelX modelZ actX actZ hposX hposZ hcard hmulX hmulZ
  have hβ : 0 < F.repairFactor * η := mul_pos (F.repairFactor_pos hone) hη
  obtain ⟨N₁, hN₁⟩ := exists_pairProduct_relation_eventually hQ T hQT hone hκone A k hk
    hδ hβ hnumerical
  obtain ⟨N₂, hN₂⟩ := F.labelsInjective
  let N : ℕ := max N₁ N₂
  have hN1 : N₁ ≤ N := le_max_left _ _
  have hNseq : N₂ ≤ seq N := (le_max_right _ _).trans (hseq N)
  have hinj : Set.InjOn (fun x : K ↦ A.map N (x, (1 : Unit))) (T : Set K) :=
    injOn_sumApproximation_map modelX modelZ actX actZ hposX hposZ hcard hmulX hmulZ T N
      (hN₂ (seq N) hNseq (bad N).i)
  have hcardPos : 0 < Fintype.card (A.model N) := by
    have hsum : Fintype.card (sumModel (modelX N) (modelZ N)) =
        Fintype.card (modelX N) + Fintype.card (modelZ N) := Fintype.card_sum
    show 0 < Fintype.card (sumModel (modelX N) (modelZ N))
    rw [hsum]
    have := hposX N
    omega
  have hlabels : multiplicativeProductLabels A N T =
      Finset.univ.image
        (sumAction (F.tags (seq N) (bad N).i) (F.tags (seq N) (bad N).l)) :=
    multiplicativeProductLabels_sumApproximation modelX modelZ actX actZ hposX hposZ
      hcard hmulX hmulZ T N
  have ha : IsEpsilonGood (A.model N) (multiplicativeProductLabels A N T) (K₀ * η)
      (bad N).b.swapPerm := by
    rw [hlabels]
    exact (bad N).swap_isEpsilonGood hK0 hK hone
  have hb : IsEpsilonGood (A.model N) (multiplicativeProductLabels A N T) (K₀ * η) 1 :=
    isEpsilonGood_one (A.model N) _ hKpos hcardPos
  obtain ⟨U, hUclose, hUboundary⟩ := hN₁ N hN1 hinj hcardPos ha hb
  rw [mul_one] at hUclose
  rw [hlabels] at hUboundary
  exact (bad N).exists_repair hone hK₀ hη hζ hηζ hkη U hUclose hUboundary

open Classical in
/-- Composites of pair-scale candidates have equivariance defects below four
times the pair threshold of their endpoints, so repair improves them. -/
theorem pairImproveCloseAt_of_pairRepairAt {K₀ h' d : ℝ} {n : ℕ} (hK₀ : 4 ≤ K₀)
    (hh0 : 0 < h') (hh : h' ≤ 1 / 100000) (hone : (1 : K) ∈ T)
    (hrep : F.PairRepairAt K₀ h' d n) : F.PairImproveCloseAt h' d n := by
  intro i j l f hf g hg
  haveI : Nonempty T := ⟨⟨1, hone⟩⟩
  obtain ⟨hfs, hft⟩ := hundred_mul_defects_le_of_candidate hf hh
  obtain ⟨hgs, hgt⟩ := hundred_mul_defects_le_of_candidate hg hh
  have hfst := card_source_le_card_target_add f
  have hfts := card_target_le_card_source_add f
  have hgst := card_source_le_card_target_add g
  have hgts := card_target_le_card_source_add g
  have hfself := hf.selfSmall
  have hgself := hg.selfSmall
  obtain ⟨hij1, hij2, hij3⟩ := nat_min_facts (F.scale n i) (F.scale n j)
  obtain ⟨hjl1, hjl2, hjl3⟩ := nat_min_facts (F.scale n j) (F.scale n l)
  obtain ⟨hil1, hil2, hil3⟩ := nat_min_facts (F.scale n i) (F.scale n l)
  have hsi : F.scale n i = Fintype.card (F.model n i) / 18 := rfl
  have hsj : F.scale n j = Fintype.card (F.model n j) / 18 := rfl
  have hsl : F.scale n l = Fintype.card (F.model n l) / 18 := rfl
  have hcomb : min (F.scale n i) (F.scale n j) + min (F.scale n j) (F.scale n l) ≤
      4 * min (F.scale n i) (F.scale n l) := by
    omega
  have hcombR : ((min (F.scale n i) (F.scale n j) : ℕ) : ℝ) +
      ((min (F.scale n j) (F.scale n l) : ℕ) : ℝ) ≤
      4 * ((min (F.scale n i) (F.scale n l) : ℕ) : ℝ) := by
    exact_mod_cast hcomb
  have hm0 : (0 : ℝ) ≤ ((min (F.scale n i) (F.scale n l) : ℕ) : ℝ) := by positivity
  have hK : 4 * h' * ((min (F.scale n i) (F.scale n l) : ℕ) : ℝ) ≤
      K₀ * h' * ((min (F.scale n i) (F.scale n l) : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK₀ hh0.le) hm0
  have hprod : h' * (((min (F.scale n i) (F.scale n j) : ℕ) : ℝ) +
      ((min (F.scale n j) (F.scale n l) : ℕ) : ℝ)) ≤
      h' * (4 * ((min (F.scale n i) (F.scale n l) : ℕ) : ℝ)) :=
    mul_le_mul_of_nonneg_left hcombR hh0.le
  have hforward : (((f.trans g).equivarianceDefect (F.tags n i) (F.tags n l)).card : ℝ) <
      K₀ * h' * ((min (F.scale n i) (F.scale n l) : ℕ) : ℝ) / 2 := by
    have h3 : (((f.trans g).equivarianceDefect (F.tags n i) (F.tags n l)).card : ℝ) ≤
        ((f.equivarianceDefect (F.tags n i) (F.tags n j)).card : ℝ) +
          ((g.equivarianceDefect (F.tags n j) (F.tags n l)).card : ℝ) := by
      exact_mod_cast card_equivarianceDefect_trans_le (F.tags n i) (F.tags n j)
        (F.tags n l) f g
    linarith only [h3, hf.forwardSmall, hg.forwardSmall, hK, hprod]
  have hbackward :
      (((f.trans g).symm.equivarianceDefect (F.tags n l) (F.tags n i)).card : ℝ) <
        K₀ * h' * ((min (F.scale n i) (F.scale n l) : ℕ) : ℝ) / 2 := by
    have h4 := card_equivarianceDefect_trans_le (F.tags n l) (F.tags n j) (F.tags n i)
      g.symm f.symm
    rw [← FinitePartialBijection.symm_trans] at h4
    have h4r : (((f.trans g).symm.equivarianceDefect (F.tags n l) (F.tags n i)).card : ℝ) ≤
        ((g.symm.equivarianceDefect (F.tags n l) (F.tags n j)).card : ℝ) +
          ((f.symm.equivarianceDefect (F.tags n j) (F.tags n i)).card : ℝ) := by
      exact_mod_cast h4
    linarith only [h4r, hf.backwardSmall, hg.backwardSmall, hK, hprod]
  exact hrep i l (f.trans g) hforward hbackward

open Classical in
/-- **Joint threshold and distance at pair scales.**  For a fixed repair factor
`K₀ ≥ 4`, the threshold `h n` and the distance factor `d n` tend to zero, `h`
dominates the prescribed vanishing sequence `ρ`, and both repair of arrows and
improvement of composites hold eventually. -/
theorem exists_joint_pairRepair (K₀ : ℝ) (hK₀ : 4 ≤ K₀)
    {Q : Finset K} {κ : ℝ} (hQ : IsKazhdanPair.{0, 0} K Q κ) (hQT : Q ⊆ T)
    (hone : (1 : K) ∈ T) (hκone : κ ≤ 1)
    (ρ : ℕ → ℝ) (hρ : Tendsto ρ atTop (𝓝 0)) :
    ∃ (h d : ℕ → ℝ), (∀ n, 0 < h n) ∧ Tendsto h atTop (𝓝 0) ∧
      Tendsto d atTop (𝓝 0) ∧ (∀ᶠ n in atTop, ρ n ≤ h n) ∧
      ∃ N₀ : ℕ, ∀ n ≥ N₀,
        F.PairRepairAt K₀ (h n) (d n) n ∧ F.PairImproveCloseAt (h n) (d n) n := by
  classical
  obtain ⟨hq0, hq1⟩ := kazhdanFactor_nonneg_lt_one hQ T hone hκone
  have hs : 0 < T.card := Finset.card_pos.mpr ⟨1, hone⟩
  have hp := F.repairFactor_pos hone
  have hK₀1 : 1 ≤ K₀ := by linarith only [hK₀]
  have hK₀pos : 0 < K₀ := by linarith only [hK₀]
  have hlevel : ∀ j : ℕ, ∃ (k : ℕ) (η δ : ℝ), 0 < k ∧ 0 < η ∧ 0 < δ ∧
      K₀ * η < 1 / (100000 * ((j : ℝ) + 1)) ∧
      (k : ℝ) ^ 2 * (K₀ * η) < 1 / (100000 * ((j : ℝ) + 1)) ∧
      16 * (T.card : ℝ) ^ 4 *
          (16 * (1 - κ ^ 2 / (4 * T.card)) ^ (2 * k) * (T.card : ℝ)⁻¹ * (K₀ * η) + δ) <
        (((1 : ℝ) / 3) * (((2 : ℝ) / 3) - (1 : ℝ) / 3) ^ 2) ^ 2 *
          (F.repairFactor * η) ^ 4 := by
    intro j
    have hζj : (0 : ℝ) < 1 / (100000 * ((j : ℝ) + 1)) / K₀ :=
      div_pos (by positivity) hK₀pos
    obtain ⟨k, η, δ, hk, hη, hδ, hηζ, hkη, hnum⟩ :=
      exists_repairParameters hq0 hq1 T.card hs (div_pos hp hK₀pos) hζj
    refine ⟨k, η, K₀ * δ, hk, hη, mul_pos hK₀pos hδ, ?_, ?_, ?_⟩
    · have h1 := (lt_div_iff₀ hK₀pos).mp hηζ
      linarith only [h1]
    · have h1 := (lt_div_iff₀ hK₀pos).mp hkη
      linarith only [h1]
    · have hmul := mul_lt_mul_of_pos_left hnum hK₀pos
      have hpη : F.repairFactor / K₀ * η * K₀ = F.repairFactor * η := by
        rw [mul_right_comm, div_mul_cancel₀ _ (ne_of_gt hK₀pos)]
      have hpow : (F.repairFactor * η) ^ 4 = (F.repairFactor / K₀ * η) ^ 4 * K₀ ^ 4 := by
        rw [← hpη, mul_pow]
      have hK4 : K₀ ≤ K₀ ^ 4 := by
        have h1 := pow_le_pow_right₀ hK₀1 (by norm_num : 1 ≤ 4)
        rwa [pow_one] at h1
      have hc0 : (0 : ℝ) ≤ (((1 : ℝ) / 3) * (((2 : ℝ) / 3) - (1 : ℝ) / 3) ^ 2) ^ 2 *
          (F.repairFactor / K₀ * η) ^ 4 := by positivity
      have hbound : K₀ * ((((1 : ℝ) / 3) * (((2 : ℝ) / 3) - (1 : ℝ) / 3) ^ 2) ^ 2 *
            (F.repairFactor / K₀ * η) ^ 4) ≤
          (((1 : ℝ) / 3) * (((2 : ℝ) / 3) - (1 : ℝ) / 3) ^ 2) ^ 2 *
            (F.repairFactor * η) ^ 4 := by
        rw [hpow]
        have h1 := mul_le_mul_of_nonneg_right hK4 hc0
        linarith only [h1]
      have hlhs : K₀ * (16 * (T.card : ℝ) ^ 4 *
            (16 * (1 - κ ^ 2 / (4 * T.card)) ^ (2 * k) * (T.card : ℝ)⁻¹ * η + δ)) =
          16 * (T.card : ℝ) ^ 4 *
            (16 * (1 - κ ^ 2 / (4 * T.card)) ^ (2 * k) * (T.card : ℝ)⁻¹ * (K₀ * η) +
              K₀ * δ) := by
        ring
      linarith only [hmul, hbound, hlhs]
  choose kf ηf δf hk hη hδ hηζ hkη hnum using hlevel
  have hζ : ∀ j : ℕ, 1 / (100000 * ((j : ℝ) + 1)) ≤ 1 / 100000 := by
    intro j
    apply one_div_le_one_div_of_le (by norm_num)
    have hj : (0 : ℝ) ≤ j := by positivity
    linarith only [hj]
  have hηle : ∀ j : ℕ, ηf j < 1 / (100000 * ((j : ℝ) + 1)) := by
    intro j
    have h1 : ηf j ≤ K₀ * ηf j := le_mul_of_one_le_left (hη j).le hK₀1
    linarith only [h1, hηζ j]
  have hevent : ∀ j : ℕ, ∃ N : ℕ, ∀ n ≥ N,
      F.PairRepairAt K₀ (ηf j) (20000 * (1 / (100000 * ((j : ℝ) + 1)))) n := by
    intro j
    exact F.eventually_pairRepairAt hQ hQT hone hκone hK₀1 (hk j) (hη j) (hδ j) (hζ j)
      (hηζ j) (hkη j) (hnum j)
  choose Nf hNf using hevent
  have hdom : ∀ j : ℕ, ∃ R : ℕ, ∀ n ≥ R, ρ n ≤ ηf j := by
    intro j
    have hev := (tendsto_order.1 hρ).2 (ηf j) (hη j)
    obtain ⟨R, hR⟩ := Filter.eventually_atTop.1 hev
    exact ⟨R, fun n hn ↦ (hR n hn).le⟩
  choose Rf hRf using hdom
  let M : ℕ → ℕ := fun j ↦
    (Finset.range (j + 1)).sup fun i ↦ max (max (Nf i) (Rf i)) i
  have hMle : ∀ j, max (max (Nf j) (Rf j)) j ≤ M j := fun j ↦
    Finset.le_sup (f := fun i ↦ max (max (Nf i) (Rf i)) i)
      (Finset.mem_range.mpr (Nat.lt_succ_self j))
  have hNM : ∀ j, Nf j ≤ M j := fun j ↦
    ((le_max_left _ _).trans (le_max_left _ _)).trans (hMle j)
  have hRM : ∀ j, Rf j ≤ M j := fun j ↦
    ((le_max_right _ _).trans (le_max_left _ _)).trans (hMle j)
  have hjM : ∀ j, j ≤ M j := fun j ↦ (le_max_right _ _).trans (hMle j)
  let J : ℕ → ℕ := fun n ↦ Nat.findGreatest (fun j ↦ M j ≤ n) n
  have hJspec : ∀ n, M 0 ≤ n → M (J n) ≤ n := fun n hn ↦
    Nat.findGreatest_spec (P := fun j ↦ M j ≤ n) (Nat.zero_le n) hn
  have hJge : ∀ n j, M j ≤ n → j ≤ J n := fun n j hj ↦
    Nat.le_findGreatest (P := fun j ↦ M j ≤ n) ((hjM j).trans hj) hj
  refine ⟨fun n ↦ ηf (J n), fun n ↦ 20000 * (1 / (100000 * ((J n : ℝ) + 1))),
    fun n ↦ hη (J n), ?_, ?_, ?_, M 0, ?_⟩
  · refine tendsto_order.2 ⟨fun a ha ↦ Filter.Eventually.of_forall fun n ↦
      lt_of_lt_of_le ha (hη (J n)).le, fun a ha ↦ ?_⟩
    obtain ⟨j, hj⟩ := exists_nat_gt (1 / a)
    rw [Filter.eventually_atTop]
    refine ⟨M j, fun n hn ↦ ?_⟩
    have hmono := one_div_antitone_nat (hJge n j hn)
    exact ((hηle (J n)).trans_le hmono).trans (one_div_lt_of_nat_gt ha hj)
  · refine tendsto_order.2 ⟨fun a ha ↦ Filter.Eventually.of_forall fun n ↦ ?_,
      fun a ha ↦ ?_⟩
    · have hpos : (0 : ℝ) < 20000 * (1 / (100000 * ((J n : ℝ) + 1))) := by positivity
      linarith only [ha, hpos]
    · have ha' : 0 < a / 20000 := by positivity
      obtain ⟨j, hj⟩ := exists_nat_gt (1 / (a / 20000))
      rw [Filter.eventually_atTop]
      refine ⟨M j, fun n hn ↦ ?_⟩
      have hmono := one_div_antitone_nat (hJge n j hn)
      have hlt := hmono.trans_lt (one_div_lt_of_nat_gt ha' hj)
      have h20 := mul_lt_mul_of_pos_left hlt (by norm_num : (0 : ℝ) < 20000)
      have hdiv : (20000 : ℝ) * (a / 20000) = a := by ring
      linarith only [h20, hdiv]
  · rw [Filter.eventually_atTop]
    exact ⟨M 0, fun n hn ↦ hRf (J n) n ((hRM (J n)).trans (hJspec n hn))⟩
  · intro n hn
    have hrep := hNf (J n) n ((hNM (J n)).trans (hJspec n hn))
    refine ⟨hrep, ?_⟩
    have hsmall : ηf (J n) ≤ 1 / 100000 := ((hηle (J n)).trans_le (hζ (J n))).le
    exact F.pairImproveCloseAt_of_pairRepairAt hK₀ (hη (J n)) hsmall hone hrep

end ComponentFamily

end CentralizerNormalizationImprove
end GroupApproximation
