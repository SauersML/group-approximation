import GroupApproximation.KunThom.RelativeFunctorImprove
import GroupApproximation.KunThom.RelativeFunctorEstimate
import GroupApproximation.KunThom.FixedPointNormalizationScaledBisection

/-!
# Small defects of the relative functor's raw map

For Kun--Thom, arXiv:2608.06222v3, Lemma 4.3, the objects of a
`ScaledPartialClusterSystem D` are disjoint blocks of an ambient model
(`BlockPatching.scaledClusterEmbedding`), labelled by `D.act`
(`BlockPatching.scaledClusterAction`), and the bridge at a retained object `X` is
realized by `u⁻¹` from `X` to `obj X`.  This file turns the word bounds of
`RelativeFunctorEstimate` into the hypotheses of
`RelativeFunctorImprove.relativeClusterFunctorOfDefects`.

* `scale_comparable_of_bridge` and `hobj_of_bridge`: a bridge with missing mass at most
  a hundredth of the source scale keeps the scales of its two objects within `11 / 10`.
* `inError` and `outError`: the localized errors of a bridge on the two sides of the raw
  map, namely the missing mass of the bridge, and for every label the compatibility
  failures, the conjugation failures and the word compatibility failures.
* `card_equivarianceDefect_raw_le` and `card_symm_equivarianceDefect_raw_le`: the word
  bounds in terms of `inError` and `outError`.
* `hforward_of_words` and `hbackward_of_words`: the defects of the raw map of a
  representative are below `K₀ h min (scale (obj X)) (scale (obj Y)) / 2` once
  `2 (1 + |L| k) ≤ K₀`, both errors at every retained object are at most `h scale / 40`
  in total, and matched scales agree within `11 / 10`.
* `relativeClusterFunctorOfWords`: the bundle of Lemma 4.3 from these inputs.
-/

namespace GroupApproximation
namespace RelativeFunctorImprove

open FinitePartialBijection GroupoidPresentation BlockPatching RelativeFunctorEstimate

universe u

/-! ### Comparable scales across a bridge -/

/-- A bridge whose missing mass is at most a hundredth of the source scale keeps the
scales of its two objects within `11 / 10`. -/
theorem scale_comparable_of_bridge {I : Type u} [Fintype I] {L : Type*} [Fintype L]
    [DecidableEq L] [Nonempty L] (D : ScaledPartialClusterSystem I L) {X X' : I}
    (w : FinitePartialBijection (D.model X) (D.model X')) {β : ℕ}
    (hw : w.sourceDefect + w.targetDefect ≤ β) (hβ : 100 * β ≤ D.scale X) :
    10 * D.scale X ≤ 11 * D.scale X' ∧ 10 * D.scale X' ≤ 11 * D.scale X := by
  have h1 := CentralizerNormalizationImprove.card_source_le_card_target_add w
  have h2 := CentralizerNormalizationImprove.card_target_le_card_source_add w
  have hX := D.scale_eq X
  have hX' := D.scale_eq X'
  have hl := D.scale_large X
  have hl' := D.scale_large X'
  constructor <;> omega

/-- **Matched scales from the bridges.**  The hypothesis `hobj` of
`ScaledPartialClusterSystem.relativeClusterFunctor` from bridge masses at most a
hundredth of the source scales. -/
theorem hobj_of_bridge {I : Type u} [Fintype I] {L : Type*} [Fintype L] [DecidableEq L]
    [Nonempty L] (D : ScaledPartialClusterSystem I L) {R S : Set I} (obj : R → S)
    (bridge : ∀ X : R, FinitePartialBijection (D.model X.1) (D.model (obj X).1))
    (β : R → ℕ)
    (hbridge : ∀ X : R, (bridge X).sourceDefect + (bridge X).targetDefect ≤ β X)
    (hβ : ∀ X : R, 100 * β X ≤ D.scale X.1) :
    ∀ X : R, 10 * D.scale X.1 ≤ 11 * D.scale (obj X).1 ∧
      10 * D.scale (obj X).1 ≤ 11 * D.scale X.1 :=
  fun X ↦ scale_comparable_of_bridge D (bridge X) (hbridge X) (hβ X)

/-! ### Localized errors of the raw map -/

/-- The errors of the bridge realized by `q` from `C` to `C'` on the incoming side of the
raw map: its missing range mass, and for every label the compatibility failures at `C'`,
the conjugation failures of `q⁻¹` at `C'`, and the word compatibility failures at `C`. -/
noncomputable def inError {Y : FiniteModel} {I : Type u} {L : Type*} [Fintype L]
    (E : BlockEmbedding Y I) (A : BlockAction E L) (q : Equiv.Perm Y) (ws : L → List L)
    (C C' : I) : ℕ :=
  ∑ s : L, ((E.bridge q C C').targetDefect + (A.compatFailure C' s).card +
    (conjFailure E q⁻¹ A (wordBlockAction A ws) C' s).card +
      (A.wordCompatFailure C (ws s)).card)

/-- The errors of the bridge realized by `q` from `D` to `D'` on the outgoing side of the
raw map: its missing source mass, and for every label the word compatibility failures at
`D`, the conjugation failures of `q` at `D`, and the compatibility failures at `D'`. -/
noncomputable def outError {Y : FiniteModel} {I : Type u} {L : Type*} [Fintype L]
    (E : BlockEmbedding Y I) (A : BlockAction E L) (q : Equiv.Perm Y) (ws : L → List L)
    (D D' : I) : ℕ :=
  ∑ s : L, ((E.bridge q D D').sourceDefect + (A.wordCompatFailure D (ws s)).card +
    (conjFailure E q (wordBlockAction A ws) A D s).card + (A.compatFailure D' s).card)

/-- **The raw map's forward defect**, from the word bound. -/
theorem card_equivarianceDefect_raw_le {Y : FiniteModel} {I : Type u} {L : Type*}
    [Fintype L] [DecidableEq L] (E : BlockEmbedding Y I) (A : BlockAction E L)
    (q : Equiv.Perm Y) (ws : L → List L) {k : ℕ} (hk : ∀ s, (ws s).length ≤ k)
    (C C' D D' : I) (f : FinitePartialBijection (E.model C) (E.model D)) :
    ((sandwich (E.bridge q C C') (E.bridge q D D') f).equivarianceDefect
        (A.blockAct C') (A.blockAct D')).card ≤
      inError E A q ws C C' +
        Fintype.card L *
          (f.sourceDefect + k * (f.equivarianceDefect (A.blockAct C) (A.blockAct D)).card) +
        outError E A q ws D D' := by
  unfold inError outError
  exact card_equivarianceDefect_sandwich_bridge_words_le E q C C' D D' A ws hk f

/-- **The raw map's backward defect**, from the word bound. -/
theorem card_symm_equivarianceDefect_raw_le {Y : FiniteModel} {I : Type u} {L : Type*}
    [Fintype L] [DecidableEq L] (E : BlockEmbedding Y I) (A : BlockAction E L)
    (q : Equiv.Perm Y) (ws : L → List L) {k : ℕ} (hk : ∀ s, (ws s).length ≤ k)
    (C C' D D' : I) (f : FinitePartialBijection (E.model C) (E.model D)) :
    ((sandwich (E.bridge q C C') (E.bridge q D D') f).symm.equivarianceDefect
        (A.blockAct D') (A.blockAct C')).card ≤
      inError E A q ws D D' +
        Fintype.card L *
          (f.targetDefect + k * (f.symm.equivarianceDefect (A.blockAct D) (A.blockAct C)).card) +
        outError E A q ws C C' := by
  unfold inError outError
  exact card_symm_equivarianceDefect_sandwich_bridge_words_le E q C C' D D' A ws hk f

/-! ### Arithmetic -/

/-- The threshold arithmetic behind `hforward_of_words` and `hbackward_of_words`, over
plain real variables. -/
theorem arith_raw {raw e₁ e₂ c sd k df h m m' sX sY K : ℝ}
    (hraw : raw ≤ e₁ + c * (sd + k * df) + e₂) (hsd : c * sd < h * m / 2)
    (hdf : df < h * m / 2) (hck : 0 ≤ c * k) (he₁ : 40 * e₁ ≤ h * sX)
    (he₂ : 40 * e₂ ≤ h * sY) (hsX : 100 * sX ≤ 121 * m') (hsY : 100 * sY ≤ 121 * m')
    (hm : 10 * m ≤ 11 * m') (hh : 0 ≤ h) (hm' : 0 ≤ m') (hK : 2 * (1 + c * k) ≤ K) :
    raw < K * h * m' / 2 := by
  have h1 : c * k * df ≤ c * k * (h * m / 2) := mul_le_mul_of_nonneg_left hdf.le hck
  have h2 : h * (10 * m) ≤ h * (11 * m') := mul_le_mul_of_nonneg_left hm hh
  have h3 : c * k * (h * (10 * m)) ≤ c * k * (h * (11 * m')) :=
    mul_le_mul_of_nonneg_left h2 hck
  have h4 : h * (100 * sX) ≤ h * (121 * m') := mul_le_mul_of_nonneg_left hsX hh
  have h5 : h * (100 * sY) ≤ h * (121 * m') := mul_le_mul_of_nonneg_left hsY hh
  have h6 : 2 * (1 + c * k) * (h * m') ≤ K * (h * m') :=
    mul_le_mul_of_nonneg_right hK (mul_nonneg hh hm')
  have h7 : 0 ≤ h * m' := mul_nonneg hh hm'
  have h8 : 0 ≤ c * k * (h * m') := mul_nonneg hck h7
  linarith

/-! ### The defect hypotheses of the bundle -/

/-- **Forward defects of the raw map.**  With the objects of `D` as blocks labelled by
`D.act`, the bridges realized by `u⁻¹`, words `ws` of length at most `k` and
`2 (1 + |L| k) ≤ K₀`: if both localized errors at every retained object total at most
`h scale / 40` and matched scales agree within `11 / 10`, then the raw map of every
representative has forward defect below `K₀ h min (scale (obj X)) (scale (obj Y)) / 2`. -/
theorem hforward_of_words {I : Type u} [Fintype I] {L : Type*} [Fintype L] [DecidableEq L]
    [Nonempty L] (D : ScaledPartialClusterSystem I L) {Y : FiniteModel}
    (ι : ∀ X, D.clusterData.model X → Y) (hinj : ∀ X, Function.Injective (ι X))
    (hdisj : ∀ (X X' : I) (x : D.clusterData.model X) (z : D.clusterData.model X'),
      ι X x = ι X' z → X = X')
    (act : L → Equiv.Perm Y) (u : Equiv.Perm Y) (ws : L → List L) {k : ℕ}
    (hk : ∀ s, (ws s).length ≤ k) (hK₀ : 2 * (1 + (Fintype.card L : ℝ) * k) ≤ D.K₀)
    {R S : Set I} (obj : R → S)
    (hobj : ∀ X : R, 10 * D.scale X.1 ≤ 11 * D.scale (obj X).1 ∧
      10 * D.scale (obj X).1 ≤ 11 * D.scale X.1)
    (herr : ∀ X : R,
      40 * ((inError (scaledClusterEmbedding D.clusterData ι hinj hdisj)
          (scaledClusterAction ι hinj hdisj act D.act) u⁻¹ ws X.1 (obj X).1 +
        outError (scaledClusterEmbedding D.clusterData ι hinj hdisj)
          (scaledClusterAction ι hinj hdisj act D.act) u⁻¹ ws X.1 (obj X).1 : ℕ) : ℝ) ≤
        D.h * D.scale X.1)
    (X Y : R) (b : D.clusterData.Rep X.1 Y.1) :
    (((sandwich ((scaledClusterEmbedding D.clusterData ι hinj hdisj).bridge u⁻¹ X.1 (obj X).1)
        ((scaledClusterEmbedding D.clusterData ι hinj hdisj).bridge u⁻¹ Y.1 (obj Y).1)
          b.1).equivarianceDefect (D.act (obj X).1) (D.act (obj Y).1)).card : ℝ) <
      D.K₀ * D.h * ((min (D.scale (obj X).1) (D.scale (obj Y).1) : ℕ) : ℝ) / 2 := by
  have hcand := (mem_clusterCandidates (D.act X.1) (D.act Y.1) D.h
    (min (D.scale X.1) (D.scale Y.1)) b.1).mp b.2
  have hraw : ((sandwich
      ((scaledClusterEmbedding D.clusterData ι hinj hdisj).bridge u⁻¹ X.1 (obj X).1)
      ((scaledClusterEmbedding D.clusterData ι hinj hdisj).bridge u⁻¹ Y.1 (obj Y).1)
        b.1).equivarianceDefect (D.act (obj X).1) (D.act (obj Y).1)).card ≤
      inError (scaledClusterEmbedding D.clusterData ι hinj hdisj)
          (scaledClusterAction ι hinj hdisj act D.act) u⁻¹ ws X.1 (obj X).1 +
        Fintype.card L *
          (b.1.sourceDefect + k * (b.1.equivarianceDefect (D.act X.1) (D.act Y.1)).card) +
        outError (scaledClusterEmbedding D.clusterData ι hinj hdisj)
          (scaledClusterAction ι hinj hdisj act D.act) u⁻¹ ws Y.1 (obj Y).1 :=
    card_equivarianceDefect_raw_le (scaledClusterEmbedding D.clusterData ι hinj hdisj)
      (scaledClusterAction ι hinj hdisj act D.act) u⁻¹ ws hk X.1 (obj X).1 Y.1 (obj Y).1 b.1
  have hraw' : (((sandwich
      ((scaledClusterEmbedding D.clusterData ι hinj hdisj).bridge u⁻¹ X.1 (obj X).1)
      ((scaledClusterEmbedding D.clusterData ι hinj hdisj).bridge u⁻¹ Y.1 (obj Y).1)
        b.1).equivarianceDefect (D.act (obj X).1) (D.act (obj Y).1)).card : ℝ) ≤
      (inError (scaledClusterEmbedding D.clusterData ι hinj hdisj)
          (scaledClusterAction ι hinj hdisj act D.act) u⁻¹ ws X.1 (obj X).1 : ℝ) +
        (Fintype.card L : ℝ) * ((b.1.sourceDefect : ℝ) +
          (k : ℝ) * ((b.1.equivarianceDefect (D.act X.1) (D.act Y.1)).card : ℝ)) +
        (outError (scaledClusterEmbedding D.clusterData ι hinj hdisj)
          (scaledClusterAction ι hinj hdisj act D.act) u⁻¹ ws Y.1 (obj Y).1 : ℝ) := by
    exact_mod_cast hraw
  have hsd := CentralizerNormalizationImprove.card_mul_sourceDefect_lt_of_candidate hcand
  have hdf := hcand.forwardSmall
  obtain ⟨hXY, hYX⟩ := D.scale_comparable_of_rep b
  obtain ⟨hXo, -⟩ := hobj X
  obtain ⟨hYo, -⟩ := hobj Y
  have hm₁ := min_le_left (D.scale X.1) (D.scale Y.1)
  have hm₂ := min_le_right (D.scale X.1) (D.scale Y.1)
  have hn₁ := min_le_left (D.scale (obj X).1) (D.scale (obj Y).1)
  have hn₂ := min_le_right (D.scale (obj X).1) (D.scale (obj Y).1)
  have hn₃ := min_choice (D.scale (obj X).1) (D.scale (obj Y).1)
  have hsXn : 100 * D.scale X.1 ≤ 121 * min (D.scale (obj X).1) (D.scale (obj Y).1) := by
    omega
  have hsYn : 100 * D.scale Y.1 ≤ 121 * min (D.scale (obj X).1) (D.scale (obj Y).1) := by
    omega
  have hmn : 10 * min (D.scale X.1) (D.scale Y.1) ≤
      11 * min (D.scale (obj X).1) (D.scale (obj Y).1) := by
    omega
  have hsXr : (100 : ℝ) * (D.scale X.1 : ℝ) ≤
      121 * ((min (D.scale (obj X).1) (D.scale (obj Y).1) : ℕ) : ℝ) := by
    exact_mod_cast hsXn
  have hsYr : (100 : ℝ) * (D.scale Y.1 : ℝ) ≤
      121 * ((min (D.scale (obj X).1) (D.scale (obj Y).1) : ℕ) : ℝ) := by
    exact_mod_cast hsYn
  have hmr : (10 : ℝ) * ((min (D.scale X.1) (D.scale Y.1) : ℕ) : ℝ) ≤
      11 * ((min (D.scale (obj X).1) (D.scale (obj Y).1) : ℕ) : ℝ) := by
    exact_mod_cast hmn
  have hX := herr X
  have hY := herr Y
  push_cast at hX hY
  have he₁ : 40 * (inError (scaledClusterEmbedding D.clusterData ι hinj hdisj)
      (scaledClusterAction ι hinj hdisj act D.act) u⁻¹ ws X.1 (obj X).1 : ℝ) ≤
        D.h * D.scale X.1 := by
    have h0 : (0 : ℝ) ≤ (outError (scaledClusterEmbedding D.clusterData ι hinj hdisj)
        (scaledClusterAction ι hinj hdisj act D.act) u⁻¹ ws X.1 (obj X).1 : ℝ) :=
      Nat.cast_nonneg _
    linarith
  have he₂ : 40 * (outError (scaledClusterEmbedding D.clusterData ι hinj hdisj)
      (scaledClusterAction ι hinj hdisj act D.act) u⁻¹ ws Y.1 (obj Y).1 : ℝ) ≤
        D.h * D.scale Y.1 := by
    have h0 : (0 : ℝ) ≤ (inError (scaledClusterEmbedding D.clusterData ι hinj hdisj)
        (scaledClusterAction ι hinj hdisj act D.act) u⁻¹ ws Y.1 (obj Y).1 : ℝ) :=
      Nat.cast_nonneg _
    linarith
  exact arith_raw hraw' hsd hdf (by positivity) he₁ he₂ hsXr hsYr hmr D.h_pos.le
    (Nat.cast_nonneg _) hK₀

/-- **Backward defects of the raw map**, under the hypotheses of `hforward_of_words`. -/
theorem hbackward_of_words {I : Type u} [Fintype I] {L : Type*} [Fintype L] [DecidableEq L]
    [Nonempty L] (D : ScaledPartialClusterSystem I L) {Y : FiniteModel}
    (ι : ∀ X, D.clusterData.model X → Y) (hinj : ∀ X, Function.Injective (ι X))
    (hdisj : ∀ (X X' : I) (x : D.clusterData.model X) (z : D.clusterData.model X'),
      ι X x = ι X' z → X = X')
    (act : L → Equiv.Perm Y) (u : Equiv.Perm Y) (ws : L → List L) {k : ℕ}
    (hk : ∀ s, (ws s).length ≤ k) (hK₀ : 2 * (1 + (Fintype.card L : ℝ) * k) ≤ D.K₀)
    {R S : Set I} (obj : R → S)
    (hobj : ∀ X : R, 10 * D.scale X.1 ≤ 11 * D.scale (obj X).1 ∧
      10 * D.scale (obj X).1 ≤ 11 * D.scale X.1)
    (herr : ∀ X : R,
      40 * ((inError (scaledClusterEmbedding D.clusterData ι hinj hdisj)
          (scaledClusterAction ι hinj hdisj act D.act) u⁻¹ ws X.1 (obj X).1 +
        outError (scaledClusterEmbedding D.clusterData ι hinj hdisj)
          (scaledClusterAction ι hinj hdisj act D.act) u⁻¹ ws X.1 (obj X).1 : ℕ) : ℝ) ≤
        D.h * D.scale X.1)
    (X Y : R) (b : D.clusterData.Rep X.1 Y.1) :
    (((sandwich ((scaledClusterEmbedding D.clusterData ι hinj hdisj).bridge u⁻¹ X.1 (obj X).1)
        ((scaledClusterEmbedding D.clusterData ι hinj hdisj).bridge u⁻¹ Y.1 (obj Y).1)
          b.1).symm.equivarianceDefect (D.act (obj Y).1) (D.act (obj X).1)).card : ℝ) <
      D.K₀ * D.h * ((min (D.scale (obj X).1) (D.scale (obj Y).1) : ℕ) : ℝ) / 2 := by
  have hcand := (mem_clusterCandidates (D.act X.1) (D.act Y.1) D.h
    (min (D.scale X.1) (D.scale Y.1)) b.1).mp b.2
  have hraw : ((sandwich
      ((scaledClusterEmbedding D.clusterData ι hinj hdisj).bridge u⁻¹ X.1 (obj X).1)
      ((scaledClusterEmbedding D.clusterData ι hinj hdisj).bridge u⁻¹ Y.1 (obj Y).1)
        b.1).symm.equivarianceDefect (D.act (obj Y).1) (D.act (obj X).1)).card ≤
      inError (scaledClusterEmbedding D.clusterData ι hinj hdisj)
          (scaledClusterAction ι hinj hdisj act D.act) u⁻¹ ws Y.1 (obj Y).1 +
        Fintype.card L *
          (b.1.targetDefect + k * (b.1.symm.equivarianceDefect (D.act Y.1) (D.act X.1)).card) +
        outError (scaledClusterEmbedding D.clusterData ι hinj hdisj)
          (scaledClusterAction ι hinj hdisj act D.act) u⁻¹ ws X.1 (obj X).1 :=
    card_symm_equivarianceDefect_raw_le (scaledClusterEmbedding D.clusterData ι hinj hdisj)
      (scaledClusterAction ι hinj hdisj act D.act) u⁻¹ ws hk X.1 (obj X).1 Y.1 (obj Y).1 b.1
  have hraw' : (((sandwich
      ((scaledClusterEmbedding D.clusterData ι hinj hdisj).bridge u⁻¹ X.1 (obj X).1)
      ((scaledClusterEmbedding D.clusterData ι hinj hdisj).bridge u⁻¹ Y.1 (obj Y).1)
        b.1).symm.equivarianceDefect (D.act (obj Y).1) (D.act (obj X).1)).card : ℝ) ≤
      (inError (scaledClusterEmbedding D.clusterData ι hinj hdisj)
          (scaledClusterAction ι hinj hdisj act D.act) u⁻¹ ws Y.1 (obj Y).1 : ℝ) +
        (Fintype.card L : ℝ) * ((b.1.targetDefect : ℝ) +
          (k : ℝ) * ((b.1.symm.equivarianceDefect (D.act Y.1) (D.act X.1)).card : ℝ)) +
        (outError (scaledClusterEmbedding D.clusterData ι hinj hdisj)
          (scaledClusterAction ι hinj hdisj act D.act) u⁻¹ ws X.1 (obj X).1 : ℝ) := by
    exact_mod_cast hraw
  have hsd := CentralizerNormalizationImprove.card_mul_targetDefect_lt_of_candidate hcand
  have hdf := hcand.backwardSmall
  obtain ⟨hXY, hYX⟩ := D.scale_comparable_of_rep b
  obtain ⟨hXo, -⟩ := hobj X
  obtain ⟨hYo, -⟩ := hobj Y
  have hm₁ := min_le_left (D.scale X.1) (D.scale Y.1)
  have hm₂ := min_le_right (D.scale X.1) (D.scale Y.1)
  have hn₁ := min_le_left (D.scale (obj X).1) (D.scale (obj Y).1)
  have hn₂ := min_le_right (D.scale (obj X).1) (D.scale (obj Y).1)
  have hn₃ := min_choice (D.scale (obj X).1) (D.scale (obj Y).1)
  have hsXn : 100 * D.scale X.1 ≤ 121 * min (D.scale (obj X).1) (D.scale (obj Y).1) := by
    omega
  have hsYn : 100 * D.scale Y.1 ≤ 121 * min (D.scale (obj X).1) (D.scale (obj Y).1) := by
    omega
  have hmn : 10 * min (D.scale X.1) (D.scale Y.1) ≤
      11 * min (D.scale (obj X).1) (D.scale (obj Y).1) := by
    omega
  have hsXr : (100 : ℝ) * (D.scale X.1 : ℝ) ≤
      121 * ((min (D.scale (obj X).1) (D.scale (obj Y).1) : ℕ) : ℝ) := by
    exact_mod_cast hsXn
  have hsYr : (100 : ℝ) * (D.scale Y.1 : ℝ) ≤
      121 * ((min (D.scale (obj X).1) (D.scale (obj Y).1) : ℕ) : ℝ) := by
    exact_mod_cast hsYn
  have hmr : (10 : ℝ) * ((min (D.scale X.1) (D.scale Y.1) : ℕ) : ℝ) ≤
      11 * ((min (D.scale (obj X).1) (D.scale (obj Y).1) : ℕ) : ℝ) := by
    exact_mod_cast hmn
  have hX := herr X
  have hY := herr Y
  push_cast at hX hY
  have he₁ : 40 * (inError (scaledClusterEmbedding D.clusterData ι hinj hdisj)
      (scaledClusterAction ι hinj hdisj act D.act) u⁻¹ ws Y.1 (obj Y).1 : ℝ) ≤
        D.h * D.scale Y.1 := by
    have h0 : (0 : ℝ) ≤ (outError (scaledClusterEmbedding D.clusterData ι hinj hdisj)
        (scaledClusterAction ι hinj hdisj act D.act) u⁻¹ ws Y.1 (obj Y).1 : ℝ) :=
      Nat.cast_nonneg _
    linarith
  have he₂ : 40 * (outError (scaledClusterEmbedding D.clusterData ι hinj hdisj)
      (scaledClusterAction ι hinj hdisj act D.act) u⁻¹ ws X.1 (obj X).1 : ℝ) ≤
        D.h * D.scale X.1 := by
    have h0 : (0 : ℝ) ≤ (inError (scaledClusterEmbedding D.clusterData ι hinj hdisj)
        (scaledClusterAction ι hinj hdisj act D.act) u⁻¹ ws X.1 (obj X).1 : ℝ) :=
      Nat.cast_nonneg _
    linarith
  exact arith_raw hraw' hsd hdf (by positivity) he₁ he₂ hsYr hsXr hmr D.h_pos.le
    (Nat.cast_nonneg _) hK₀

/-! ### The relative cluster functor from word bounds -/

/-- **Kun–Thom, Lemma 4.3, on a scaled cluster system, from word bounds.**  The objects
of `D` are blocks of an ambient model labelled by `D.act`; the bridge at a retained
object is realized by `u⁻¹`; the words `ws` have length at most `k` and
`2 (1 + |L| k) ≤ K₀`.  The remaining inputs are bridge masses at most a hundredth of the
scales, localized errors at most `h scale / 40`, the distance factor
`0 ≤ d ≤ 1 / 5000`, and retained scales at least `400`. -/
noncomputable def relativeClusterFunctorOfWords {I : Type u} [Fintype I] {L : Type*}
    [Fintype L] [DecidableEq L] [Nonempty L] (D : ScaledPartialClusterSystem I L)
    {Y : FiniteModel} (ι : ∀ X, D.clusterData.model X → Y)
    (hinj : ∀ X, Function.Injective (ι X))
    (hdisj : ∀ (X X' : I) (x : D.clusterData.model X) (z : D.clusterData.model X'),
      ι X x = ι X' z → X = X')
    (act : L → Equiv.Perm Y) (u : Equiv.Perm Y) (ws : L → List L) {k : ℕ}
    (hk : ∀ s, (ws s).length ≤ k) (hK₀ : 2 * (1 + (Fintype.card L : ℝ) * k) ≤ D.K₀)
    {R S : Finset I} (π : I → I) (hmaps : Set.MapsTo π S R) (hinjπ : Set.InjOn π S)
    (hsurj : Set.SurjOn π S R) (β : ↥(R : Set I) → ℕ)
    (hbridge : ∀ X : (R : Set I),
      ((scaledClusterEmbedding D.clusterData ι hinj hdisj).bridge u⁻¹ X.1
          (ClusterMetric.matchingInverse π hsurj X).1).sourceDefect +
        ((scaledClusterEmbedding D.clusterData ι hinj hdisj).bridge u⁻¹ X.1
          (ClusterMetric.matchingInverse π hsurj X).1).targetDefect ≤ β X)
    (hβ : ∀ X : (R : Set I), 100 * β X ≤ D.scale X.1)
    (herr : ∀ X : (R : Set I),
      40 * ((inError (scaledClusterEmbedding D.clusterData ι hinj hdisj)
          (scaledClusterAction ι hinj hdisj act D.act) u⁻¹ ws X.1
            (ClusterMetric.matchingInverse π hsurj X).1 +
        outError (scaledClusterEmbedding D.clusterData ι hinj hdisj)
          (scaledClusterAction ι hinj hdisj act D.act) u⁻¹ ws X.1
            (ClusterMetric.matchingInverse π hsurj X).1 : ℕ) : ℝ) ≤
        D.h * D.scale X.1)
    (hd0 : 0 ≤ D.d) (hd : D.d ≤ 1 / 5000)
    (hscale : ∀ X : (R : Set I), 400 ≤ D.scale X.1) :
    D.presentation.RelativeClusterFunctor R S :=
  relativeClusterFunctorOfDefects D π hmaps hinjπ hsurj
    (fun X ↦ (scaledClusterEmbedding D.clusterData ι hinj hdisj).bridge u⁻¹ X.1
      (ClusterMetric.matchingInverse π hsurj X).1)
    β hbridge
    (hforward_of_words D ι hinj hdisj act u ws hk hK₀ (ClusterMetric.matchingInverse π hsurj)
      (hobj_of_bridge D (ClusterMetric.matchingInverse π hsurj)
        (fun X ↦ (scaledClusterEmbedding D.clusterData ι hinj hdisj).bridge u⁻¹ X.1
          (ClusterMetric.matchingInverse π hsurj X).1) β hbridge hβ) herr)
    (hbackward_of_words D ι hinj hdisj act u ws hk hK₀ (ClusterMetric.matchingInverse π hsurj)
      (hobj_of_bridge D (ClusterMetric.matchingInverse π hsurj)
        (fun X ↦ (scaledClusterEmbedding D.clusterData ι hinj hdisj).bridge u⁻¹ X.1
          (ClusterMetric.matchingInverse π hsurj X).1) β hbridge hβ) herr)
    hβ
    (hobj_of_bridge D (ClusterMetric.matchingInverse π hsurj)
      (fun X ↦ (scaledClusterEmbedding D.clusterData ι hinj hdisj).bridge u⁻¹ X.1
        (ClusterMetric.matchingInverse π hsurj X).1) β hbridge hβ)
    hd0 hd hscale

end RelativeFunctorImprove
end GroupApproximation
