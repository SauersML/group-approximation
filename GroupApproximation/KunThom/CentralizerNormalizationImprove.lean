import GroupApproximation.KunThom.CentralizerNormalizationSumApproximation
import GroupApproximation.KunThom.CentralizerNormalizationParameters
import GroupApproximation.KunThom.KunThomRounding
import GroupApproximation.Kun.KunFiniteMarkov

/-!
# Uniform improvement of cluster candidates on expander components

A `ComponentFamily` is a sequence of finite families of component models, each
carrying approximate actions of a Kazhdan group `K` with an exact directed
Cheeger bound for the labels of a finite set `T`, sizes tending to infinity,
local multiplicativity and injective labels.  An object `i` at index `n` has
cluster scale `|model n i| / 18`.

`eventually_improveCloseAt` proves, for fixed improvement parameters, that
eventually every composite `f.trans g` of two cluster candidates at threshold
`η` has an improving candidate at the scale of its source object, within
`20000 ζ |model|`.  The proof is by contradiction.  A sequence of
counterexamples, one per index, packs into one multiplicative approximation on
the unions of source and target components.  The proved Kun--Thom relation
improvement (`KunThomRounding.exists_pairProduct_relation_eventually`) then
supplies relations near the swap graphs with small boundary, and the finite
repair step (`CentralizerNormalizationCrossingRepair`) turns them into
improving candidates (`BadTriple.exists_improvement`).

`exists_joint_improvement` chooses the threshold and distance along a
diagonal of parameter levels.  Both tend to zero, and the threshold dominates
any prescribed vanishing error sequence.
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

/-! ### Candidate numerics -/

theorem card_mul_sourceDefect_lt_of_candidate {L : Type*} [Fintype L] [DecidableEq L]
    {Y Z : FiniteModel} {actY : L → Equiv.Perm Y} {actZ : L → Equiv.Perm Z}
    {h : ℝ} {m : ℕ} {f : FinitePartialBijection Y Z}
    (hf : f.IsClusterCandidate actY actZ h m) :
    (Fintype.card L : ℝ) * f.sourceDefect < h * m / 2 := by
  have h1 := card_mul_sourceDefect_le_card_equivarianceDefect f actY actZ
  have h1r : (Fintype.card L : ℝ) * (f.sourceDefect : ℝ) ≤
      ((f.equivarianceDefect actY actZ).card : ℝ) := by
    exact_mod_cast h1
  exact h1r.trans_lt hf.forwardSmall

theorem card_mul_targetDefect_lt_of_candidate {L : Type*} [Fintype L] [DecidableEq L]
    {Y Z : FiniteModel} {actY : L → Equiv.Perm Y} {actZ : L → Equiv.Perm Z}
    {h : ℝ} {m : ℕ} {f : FinitePartialBijection Y Z}
    (hf : f.IsClusterCandidate actY actZ h m) :
    (Fintype.card L : ℝ) * f.targetDefect < h * m / 2 := by
  have h1 := card_mul_targetDefect_le_card_symm_equivarianceDefect f actY actZ
  have h1r : (Fintype.card L : ℝ) * (f.targetDefect : ℝ) ≤
      ((f.symm.equivarianceDefect actZ actY).card : ℝ) := by
    exact_mod_cast h1
  exact h1r.trans_lt hf.backwardSmall

/-- A candidate below a tiny threshold misses at most a hundredth of its scale. -/
theorem hundred_mul_defects_le_of_candidate {L : Type*} [Fintype L] [DecidableEq L]
    [Nonempty L] {Y Z : FiniteModel} {actY : L → Equiv.Perm Y}
    {actZ : L → Equiv.Perm Z} {h : ℝ} {m : ℕ} {f : FinitePartialBijection Y Z}
    (hf : f.IsClusterCandidate actY actZ h m) (hh : h ≤ 1 / 100000) :
    100 * f.sourceDefect ≤ m ∧ 100 * f.targetDefect ≤ m := by
  have hL : (1 : ℝ) ≤ Fintype.card L := by exact_mod_cast Fintype.card_pos
  have hs := card_mul_sourceDefect_lt_of_candidate hf
  have ht := card_mul_targetDefect_lt_of_candidate hf
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hsd0 : (0 : ℝ) ≤ f.sourceDefect := by positivity
  have htd0 : (0 : ℝ) ≤ f.targetDefect := by positivity
  have hhm : h * m ≤ m / 100000 := by nlinarith only [hh, hm0]
  refine ⟨?_, ?_⟩
  · have hsd : (f.sourceDefect : ℝ) ≤ Fintype.card L * f.sourceDefect := by
      nlinarith only [hL, hsd0]
    have hreal : (100 * f.sourceDefect : ℝ) ≤ m := by
      linarith only [hs, hsd, hhm, hm0]
    exact_mod_cast hreal
  · have htd : (f.targetDefect : ℝ) ≤ Fintype.card L * f.targetDefect := by
      nlinarith only [hL, htd0]
    have hreal : (100 * f.targetDefect : ℝ) ≤ m := by
      linarith only [ht, htd, hhm, hm0]
    exact_mod_cast hreal

theorem card_target_le_card_source_add {Y Z : FiniteModel}
    (f : FinitePartialBijection Y Z) :
    Fintype.card Z ≤ Fintype.card Y + f.targetDefect := by
  have hst := f.card_source_eq_card_target
  have hs : f.source.card ≤ Fintype.card Y := Finset.card_le_univ _
  have ht : f.target.card ≤ Fintype.card Z := Finset.card_le_univ _
  unfold targetDefect
  omega

theorem card_source_le_card_target_add {Y Z : FiniteModel}
    (f : FinitePartialBijection Y Z) :
    Fintype.card Y ≤ Fintype.card Z + f.sourceDefect := by
  have hst := f.card_source_eq_card_target
  have hs : f.source.card ≤ Fintype.card Y := Finset.card_le_univ _
  have ht : f.target.card ≤ Fintype.card Z := Finset.card_le_univ _
  unfold sourceDefect
  omega

/-! ### Real arithmetic, stated over plain variables -/

theorem arith_four_defects {a b c d mX mY η : ℝ} (ha : a < η * mX / 2)
    (hb : b < η * mY / 2) (hc : c < η * mY / 2) (hd : d < η * mX / 2)
    (hmY : mY ≤ 2 * mX) (hη : 0 < η) : a + b + (c + d) < 3 * η * mX := by
  have hprod : η * mY ≤ η * (2 * mX) := mul_le_mul_of_nonneg_left hmY hη.le
  linarith only [ha, hb, hc, hd, hprod]

theorem arith_good {arcs s η mX W : ℝ} (h1 : arcs ≤ s) (h2 : s < 3 * η * mX)
    (hW : 18 * mX ≤ W) (hη : 0 < η) (hmX : 0 ≤ mX) : arcs < η * W := by
  have hprod : η * (18 * mX) ≤ η * W := mul_le_mul_of_nonneg_left hW hη.le
  have hpos : 0 ≤ η * mX := mul_nonneg hη.le hmX
  linarith only [h1, h2, hprod, hpos]

theorem arith_edits {E k2 s η W ζ mX : ℝ} (hE : E < 36 * k2 * s⁻¹ * η * W)
    (hs : 1 ≤ s) (hkη : k2 * η < ζ) (hW : W ≤ 90 * mX) (hW0 : 0 ≤ W)
    (hk2 : 0 ≤ k2) (hη : 0 ≤ η) (hζ : 0 ≤ ζ) : E < 3240 * ζ * mX := by
  have h1 : 36 * k2 * s⁻¹ * η * W ≤ 36 * (k2 * η) * W := by
    rw [show 36 * k2 * s⁻¹ * η * W = 36 * (k2 * η) * W / s by ring]
    exact div_le_self (mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg hk2 hη)) hW0) hs
  have h2 : 36 * (k2 * η) * W ≤ 36 * ζ * (90 * mX) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hkη.le (by norm_num)) hW hW0
      (mul_nonneg (by norm_num) hζ)
  linarith only [hE, h1, h2]

theorem arith_hundred_edits {E ζ mX : ℝ} (hE : E < 3240 * ζ * mX)
    (hζ : ζ ≤ 1 / 100000) (hmX : 1 ≤ mX) : 100 * E < 4 * mX := by
  have hprod : ζ * mX ≤ (1 / 100000) * mX :=
    mul_le_mul_of_nonneg_right hζ (by linarith only [hmX])
  linarith only [hE, hprod, hmX]

theorem arith_forward {c s SW B p η W mX : ℝ} (hc : 0 < c) (hs : 1 ≤ s)
    (hSW : SW ≤ s) (hB0 : 0 ≤ B) (hB : B < p * η * W) (hpη : 0 ≤ p * η)
    (hW : W ≤ 90 * mX) (hid : (2 + c) * s * (c + 7 * s) * p = c ^ 2 / 360)
    (hη : 0 < η) (hmX : 1 ≤ mX) :
    (2 * s + c * s) * ((c + 7 * SW) * B) < c * c * (η * mX / 2) := by
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
  have hprod : 0 < c ^ 2 * η * mX :=
    mul_pos (mul_pos (pow_pos hc 2) hη) (by linarith only [hmX])
  rw [hid] at step4
  have step5 : 90 * η * mX * (c ^ 2 / 360) = c ^ 2 * η * mX / 4 := by ring
  have step6 : c * c * (η * mX / 2) = c ^ 2 * η * mX / 2 := by ring
  linarith only [step1, step2, step3, step4, step5, step6, hprod]

theorem arith_distance {D dsum E η ζ mX X : ℝ} (hD : D ≤ dsum + 6 * E)
    (hdsum : dsum < 3 * η * mX) (hE : E < 3240 * ζ * mX) (hηζ : η < ζ)
    (hmX : 0 ≤ mX) (hX : mX ≤ X) (hζ : 0 ≤ ζ) : D ≤ 20000 * ζ * X := by
  have h1 : η * mX ≤ ζ * mX := mul_le_mul_of_nonneg_right hηζ.le hmX
  have h2 : ζ * mX ≤ ζ * X := mul_le_mul_of_nonneg_left hX hζ
  have h3 : 0 ≤ ζ * mX := mul_nonneg hζ hmX
  linarith only [hD, hdsum, hE, h1, h2, h3]

theorem arith_defect_sum {sT a b c d mX mY η : ℝ} (hsT : 1 ≤ sT)
    (ha : sT * a < η * mX / 2) (hb : sT * b < η * mY / 2)
    (hc : sT * c < η * mY / 2) (hd : sT * d < η * mX / 2)
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hc0 : 0 ≤ c) (hd0 : 0 ≤ d)
    (hmY : mY ≤ 2 * mX) (hη : 0 < η) : a + b + (c + d) < 3 * η * mX := by
  have ha' : a ≤ sT * a := by nlinarith only [hsT, ha0]
  have hb' : b ≤ sT * b := by nlinarith only [hsT, hb0]
  have hc' : c ≤ sT * c := by nlinarith only [hsT, hc0]
  have hd' : d ≤ sT * d := by nlinarith only [hsT, hd0]
  have hprod : η * mY ≤ η * (2 * mX) := mul_le_mul_of_nonneg_left hmY hη.le
  linarith only [ha, hb, hc, hd, ha', hb', hc', hd', hprod]

/-! ### Component families -/

/-- Finite families of expander component models with approximate actions. -/
structure ComponentFamily (K : Type) [Group K] (T : Finset K) where
  index : ℕ → Type
  model : ∀ n, index n → FiniteModel
  act : ∀ n (i : index n), K → Equiv.Perm (model n i)
  cheeger : ℝ
  cheeger_pos : 0 < cheeger
  expands : ∀ n (i : index n),
    DirectedCoarea.HasCheegerLowerBound (model n i) (T.image (act n i)) cheeger
  size_tendsTo : ∀ M : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∀ i : index n,
    M ≤ Fintype.card (model n i)
  locallyMultiplicative : ∀ (g h : K) (ε : ℝ), 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
    ∀ i : index n,
      hammingDistance (model n i) (act n i (g * h)) (act n i g * act n i h) < ε
  labelsInjective : ∃ N : ℕ, ∀ n ≥ N, ∀ i : index n,
    Set.InjOn (act n i) (T : Set K)

namespace ComponentFamily

variable {K : Type} [Group K] {T : Finset K} (F : ComponentFamily K T)

/-- The generator tags acting on an object. -/
def tags (n : ℕ) (i : F.index n) : T → Equiv.Perm (F.model n i) :=
  fun t ↦ F.act n i t.1

/-- The cluster scale of an object. -/
def scale (n : ℕ) (i : F.index n) : ℕ := Fintype.card (F.model n i) / 18

/-- The boundary factor of the improvement parameters. -/
noncomputable def repairFactor : ℝ :=
  F.cheeger ^ 2 / (360 * (2 + F.cheeger) * T.card * (F.cheeger + 7 * T.card))

theorem repairFactor_pos (hone : (1 : K) ∈ T) : 0 < F.repairFactor := by
  have hc := F.cheeger_pos
  have hT : (0 : ℝ) < T.card := by exact_mod_cast Finset.card_pos.mpr ⟨1, hone⟩
  unfold repairFactor
  positivity

theorem repairFactor_identity (hone : (1 : K) ∈ T) :
    (2 + F.cheeger) * (T.card : ℝ) * (F.cheeger + 7 * T.card) * F.repairFactor =
      F.cheeger ^ 2 / 360 := by
  have hc := F.cheeger_pos
  have hT : (0 : ℝ) < T.card := by exact_mod_cast Finset.card_pos.mpr ⟨1, hone⟩
  have hD : (360 * (2 + F.cheeger) * (T.card : ℝ) * (F.cheeger + 7 * T.card)) ≠ 0 := by
    positivity
  unfold repairFactor
  rw [mul_div_assoc', div_eq_div_iff hD (by norm_num : (360 : ℝ) ≠ 0)]
  ring

open Classical in
theorem univ_image_tags (n : ℕ) (i : F.index n) :
    Finset.univ.image (F.tags n i) = T.image (F.act n i) := by
  ext σ
  constructor
  · intro hσ
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hσ
    exact Finset.mem_image.mpr ⟨t.1, t.2, rfl⟩
  · intro hσ
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hσ
    exact Finset.mem_image.mpr ⟨⟨k, hk⟩, Finset.mem_univ _, rfl⟩

open Classical in
/-- Improvement of composites of candidates at index `n`, threshold `h'` and
distance factor `d`, each arrow at the scale of its source object. -/
def ImproveCloseAt (h' d : ℝ) (n : ℕ) : Prop :=
  ∀ (i j l : F.index n)
    (f : FinitePartialBijection (F.model n i) (F.model n j)),
    f.IsClusterCandidate (F.tags n i) (F.tags n j) h' (F.scale n i) →
    ∀ g : FinitePartialBijection (F.model n j) (F.model n l),
    g.IsClusterCandidate (F.tags n j) (F.tags n l) h' (F.scale n j) →
    ∃ r : FinitePartialBijection (F.model n i) (F.model n l),
      r.IsClusterCandidate (F.tags n i) (F.tags n l) h' (F.scale n i) ∧
        r.twoSidedDisagreement (f.trans g) < 2 * F.scale n i ∧
        (r.twoSidedDisagreement (f.trans g) : ℝ) ≤ d * Fintype.card (F.model n i)

open Classical in
/-- A counterexample to improvement at index `n`. -/
structure BadTriple (h' d : ℝ) (n : ℕ) where
  i : F.index n
  j : F.index n
  l : F.index n
  f : FinitePartialBijection (F.model n i) (F.model n j)
  hf : f.IsClusterCandidate (F.tags n i) (F.tags n j) h' (F.scale n i)
  g : FinitePartialBijection (F.model n j) (F.model n l)
  hg : g.IsClusterCandidate (F.tags n j) (F.tags n l) h' (F.scale n j)
  noImprove : ∀ r : FinitePartialBijection (F.model n i) (F.model n l),
    ¬ (r.IsClusterCandidate (F.tags n i) (F.tags n l) h' (F.scale n i) ∧
      r.twoSidedDisagreement (f.trans g) < 2 * F.scale n i ∧
      (r.twoSidedDisagreement (f.trans g) : ℝ) ≤ d * Fintype.card (F.model n i))

theorem improveCloseAt_of_not_nonempty {h' d : ℝ} {n : ℕ}
    (h : ¬ Nonempty (F.BadTriple h' d n)) : F.ImproveCloseAt h' d n := by
  classical
  intro i j l f hf g hg
  by_contra hno
  exact h ⟨⟨i, j, l, f, hf, g, hg, fun r hr ↦ hno ⟨r, hr⟩⟩⟩

namespace BadTriple

variable {F}

open Classical in
/-- Natural-number size facts for a counterexample. -/
theorem sizes {h' d : ℝ} {n : ℕ} (B : F.BadTriple h' d n) (hh : h' ≤ 1 / 100000)
    (hone : (1 : K) ∈ T) :
    1 ≤ F.scale n B.i ∧
      18 * F.scale n B.i ≤ Fintype.card (F.model n B.i) ∧
      Fintype.card (F.model n B.i) + Fintype.card (F.model n B.l) ≤ 90 * F.scale n B.i ∧
      17 * F.scale n B.i ≤ Fintype.card (F.model n B.l) ∧
      F.scale n B.j ≤ 2 * F.scale n B.i := by
  haveI : Nonempty T := ⟨⟨1, hone⟩⟩
  have hX : 1 ≤ F.scale n B.i := by
    have h := B.hf.selfSmall
    omega
  obtain ⟨hfs, hft⟩ := hundred_mul_defects_le_of_candidate B.hf hh
  obtain ⟨hgs, hgt⟩ := hundred_mul_defects_le_of_candidate B.hg hh
  have hY1 := card_target_le_card_source_add B.f
  have hY2 := card_source_le_card_target_add B.f
  have hZ1 := card_target_le_card_source_add B.g
  have hZ2 := card_source_le_card_target_add B.g
  have hsi : F.scale n B.i = Fintype.card (F.model n B.i) / 18 := rfl
  have hsj : F.scale n B.j = Fintype.card (F.model n B.j) / 18 := rfl
  omega

open Classical in
/-- The swap encoding of the composite of a counterexample is good for the
union labels. -/
theorem swap_isEpsilonGood {η d : ℝ} {n : ℕ} (B : F.BadTriple η d n) (hη : 0 < η)
    (hh : η ≤ 1 / 100000) (hone : (1 : K) ∈ T) :
    IsEpsilonGood (sumModel (F.model n B.i) (F.model n B.l))
      (Finset.univ.image (sumAction (F.tags n B.i) (F.tags n B.l))) η
      (B.f.trans B.g).swapPerm := by
  obtain ⟨_, h18, _, _, hmY⟩ := B.sizes hh hone
  have hmYr : (F.scale n B.j : ℝ) ≤ 2 * (F.scale n B.i : ℝ) := by exact_mod_cast hmY
  have hsum4 := arith_four_defects B.hf.forwardSmall B.hg.forwardSmall
    B.hg.backwardSmall B.hf.backwardSmall hmYr hη
  have hsum : Fintype.card (sumModel (F.model n B.i) (F.model n B.l)) =
      Fintype.card (F.model n B.i) + Fintype.card (F.model n B.l) := Fintype.card_sum
  have hWnat : 18 * F.scale n B.i ≤ Fintype.card (sumModel (F.model n B.i) (F.model n B.l)) := by
    rw [hsum]
    omega
  have hW : 18 * (F.scale n B.i : ℝ) ≤
      (Fintype.card (sumModel (F.model n B.i) (F.model n B.l)) : ℝ) := by
    exact_mod_cast hWnat
  have hmX0 : (0 : ℝ) ≤ F.scale n B.i := by positivity
  refine ⟨?_, ?_⟩
  · have hc :
        ((badArcs (sumModel (F.model n B.i) (F.model n B.l))
          (Finset.univ.image (sumAction (F.tags n B.i) (F.tags n B.l)))
          (B.f.trans B.g).swapPerm).card : ℝ) ≤
        ((B.f.equivarianceDefect (F.tags n B.i) (F.tags n B.j)).card : ℝ) +
          ((B.g.equivarianceDefect (F.tags n B.j) (F.tags n B.l)).card : ℝ) +
          (((B.g.symm.equivarianceDefect (F.tags n B.l) (F.tags n B.j)).card : ℝ) +
            ((B.f.symm.equivarianceDefect (F.tags n B.j) (F.tags n B.i)).card : ℝ)) := by
      exact_mod_cast card_badArcs_swap_trans_le (F.tags n B.i) (F.tags n B.j)
        (F.tags n B.l) B.f B.g
    exact arith_good hc hsum4 hW hη hmX0
  · have hc :
        ((badArcs (sumModel (F.model n B.i) (F.model n B.l))
          (Finset.univ.image (sumAction (F.tags n B.i) (F.tags n B.l)))
          (B.f.trans B.g).swapPerm⁻¹).card : ℝ) ≤
        ((B.f.equivarianceDefect (F.tags n B.i) (F.tags n B.j)).card : ℝ) +
          ((B.g.equivarianceDefect (F.tags n B.j) (F.tags n B.l)).card : ℝ) +
          (((B.g.symm.equivarianceDefect (F.tags n B.l) (F.tags n B.j)).card : ℝ) +
            ((B.f.symm.equivarianceDefect (F.tags n B.j) (F.tags n B.i)).card : ℝ)) := by
      exact_mod_cast card_badArcs_swap_trans_inv_le (F.tags n B.i) (F.tags n B.j)
        (F.tags n B.l) B.f B.g
    exact arith_good hc hsum4 hW hη hmX0

open Classical in
/-- **A relation near the swap graph with small boundary contradicts the
counterexample.** -/
theorem exists_improvement {η ζ : ℝ} {k n : ℕ} (B : F.BadTriple η (20000 * ζ) n)
    (hone : (1 : K) ∈ T) (hη : 0 < η) (hζ : ζ ≤ 1 / 100000) (hηζ : η < ζ)
    (hkη : (k : ℝ) ^ 2 * η < ζ)
    (U : Finset (sumModel (F.model n B.i) (F.model n B.l) ×
      sumModel (F.model n B.i) (F.model n B.l)))
    (hUclose : ((U ∆ permutationGraph (sumModel (F.model n B.i) (F.model n B.l))
        (B.f.trans B.g).swapPerm).card : ℝ) <
      36 * (k : ℝ) ^ 2 * (T.card : ℝ)⁻¹ * η *
        (Fintype.card (sumModel (F.model n B.i) (F.model n B.l)) : ℝ))
    (hUboundary : ((relationBoundary (sumModel (F.model n B.i) (F.model n B.l))
        (Finset.univ.image (sumAction (F.tags n B.i) (F.tags n B.l))) U).card : ℝ) <
      F.repairFactor * η *
        (Fintype.card (sumModel (F.model n B.i) (F.model n B.l)) : ℝ)) :
    False := by
  haveI : Nonempty T := ⟨⟨1, hone⟩⟩
  have hηsmall : η ≤ 1 / 100000 := by linarith only [hζ, hηζ]
  obtain ⟨hX1, h18, h90, h17, hmY⟩ := B.sizes hηsmall hone
  have hc := F.cheeger_pos
  have hTc : (1 : ℝ) ≤ T.card := by exact_mod_cast Finset.card_pos.mpr ⟨(1 : K), hone⟩
  have hsT : (1 : ℝ) ≤ Fintype.card T := by rw [Fintype.card_coe]; exact hTc
  have hζ0 : 0 ≤ ζ := by
    have hk2 : (0 : ℝ) ≤ (k : ℝ) ^ 2 * η := mul_nonneg (by positivity) hη.le
    linarith only [hkη, hk2]
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
  have hmX1 : (1 : ℝ) ≤ F.scale n B.i := by exact_mod_cast hX1
  have hmYr : (F.scale n B.j : ℝ) ≤ 2 * (F.scale n B.i : ℝ) := by exact_mod_cast hmY
  -- The edit count.
  have hE := arith_edits hUclose hTc hkη hWr hW0 (by positivity) hη.le hζ0
  have hE100 : 100 * (U ∆ permutationGraph (sumModel (F.model n B.i) (F.model n B.l))
      (B.f.trans B.g).swapPerm).card < 4 * F.scale n B.i := by
    have hreal := arith_hundred_edits hE hζ hmX1
    exact_mod_cast hreal
  have hEdits :
      (permutationGraph (sumModel (F.model n B.i) (F.model n B.l))
          (B.f.trans B.g).swapPerm \ U).card +
        (U \ permutationGraph (sumModel (F.model n B.i) (F.model n B.l))
          (B.f.trans B.g).swapPerm).card ≤
      (U ∆ permutationGraph (sumModel (F.model n B.i) (F.model n B.l))
          (B.f.trans B.g).swapPerm).card :=
    le_of_eq (card_sdiff_add_card_sdiff_eq_symmDiff U
      (permutationGraph (sumModel (F.model n B.i) (F.model n B.l))
        (B.f.trans B.g).swapPerm))
  -- Defects of the composite.
  have hfd := hundred_mul_defects_le_of_candidate B.hf hηsmall
  have hgd := hundred_mul_defects_le_of_candidate B.hg hηsmall
  have hbs := sourceDefect_trans_le B.f B.g
  have hbt := targetDefect_trans_le B.f B.g
  have hsmallX :
      2 * ((B.f.trans B.g).sourceDefect +
        3 * (U ∆ permutationGraph (sumModel (F.model n B.i) (F.model n B.l))
          (B.f.trans B.g).swapPerm).card) ≤ Fintype.card (F.model n B.i) := by
    omega
  have hsmallZ :
      2 * ((B.f.trans B.g).targetDefect +
        3 * (U ∆ permutationGraph (sumModel (F.model n B.i) (F.model n B.l))
          (B.f.trans B.g).swapPerm).card) ≤ Fintype.card (F.model n B.l) := by
    omega
  have hclose :
      (B.f.trans B.g).sourceDefect + (B.f.trans B.g).targetDefect +
          6 * (U ∆ permutationGraph (sumModel (F.model n B.i) (F.model n B.l))
            (B.f.trans B.g).swapPerm).card < 2 * F.scale n B.i := by
    omega
  -- The boundary inequality.
  have hSWnat : (Finset.univ.image (sumAction (F.tags n B.i) (F.tags n B.l))).card ≤
      T.card :=
    Finset.card_image_le.trans (Finset.card_univ.trans (Fintype.card_coe T)).le
  have hSW : ((Finset.univ.image (sumAction (F.tags n B.i) (F.tags n B.l))).card : ℝ) ≤
      T.card := by exact_mod_cast hSWnat
  have hB0 : (0 : ℝ) ≤ ((relationBoundary (sumModel (F.model n B.i) (F.model n B.l))
      (Finset.univ.image (sumAction (F.tags n B.i) (F.tags n B.l))) U).card : ℝ) := by
    positivity
  have hpη : 0 ≤ F.repairFactor * η := (mul_pos (F.repairFactor_pos hone) hη).le
  have hforwardT := arith_forward hc hTc hSW hB0 hUboundary hpη hWr
    (F.repairFactor_identity hone) hη hmX1
  have hforward :
      (2 * (Fintype.card T : ℝ) + F.cheeger * Fintype.card T) *
          ((F.cheeger + 7 * (Finset.univ.image
              (sumAction (F.tags n B.i) (F.tags n B.l))).card) *
            ((relationBoundary (sumModel (F.model n B.i) (F.model n B.l))
              (Finset.univ.image (sumAction (F.tags n B.i) (F.tags n B.l))) U).card : ℝ)) <
        F.cheeger * F.cheeger * (η * F.scale n B.i / 2) := by
    rw [Fintype.card_coe]
    exact hforwardT
  -- The repair step.
  have hXcheeger : DirectedCoarea.HasCheegerLowerBound (F.model n B.i)
      (Finset.univ.image (F.tags n B.i)) F.cheeger := by
    rw [F.univ_image_tags]
    exact F.expands n B.i
  have hZcheeger : DirectedCoarea.HasCheegerLowerBound (F.model n B.l)
      (Finset.univ.image (F.tags n B.l)) F.cheeger := by
    rw [F.univ_image_tags]
    exact F.expands n B.l
  have hrep := repairRelation_extractCrossing_candidate_and_close
    (F.tags n B.i) (F.tags n B.l) hXcheeger hZcheeger (B.f.trans B.g) U _ hEdits
    hsmallX hsmallZ hclose hforward
  -- The distance bound.
  have hham :
      (hammingDisagreement (B.f.trans B.g).swapPerm
        (repairRelation (sumModel (F.model n B.i) (F.model n B.l)) U)).card ≤
      3 * (U ∆ permutationGraph (sumModel (F.model n B.i) (F.model n B.l))
          (B.f.trans B.g).swapPerm).card := by
    have h := card_repairRelation_disagreement_le
      (sumModel (F.model n B.i) (F.model n B.l)) U (B.f.trans B.g).swapPerm
    rw [card_hammingDisagreement_comm]
    omega
  have hhamInv :
      (hammingDisagreement (B.f.trans B.g).swapPerm⁻¹
        (repairRelation (sumModel (F.model n B.i) (F.model n B.l)) U)⁻¹).card ≤
      3 * (U ∆ permutationGraph (sumModel (F.model n B.i) (F.model n B.l))
          (B.f.trans B.g).swapPerm).card := by
    rw [card_hammingDisagreement_inv]
    exact hham
  have hdist := twoSidedDisagreement_extractCrossing_le (B.f.trans B.g)
    (repairRelation (sumModel (F.model n B.i) (F.model n B.l)) U)
  have hdistNat :
      (B.f.trans B.g).twoSidedDisagreement
          (extractCrossing (repairRelation (sumModel (F.model n B.i) (F.model n B.l)) U)) ≤
        (B.f.sourceDefect + B.g.sourceDefect + (B.g.targetDefect + B.f.targetDefect)) +
          6 * (U ∆ permutationGraph (sumModel (F.model n B.i) (F.model n B.l))
            (B.f.trans B.g).swapPerm).card := by
    omega
  have hdistReal :
      (((B.f.trans B.g).twoSidedDisagreement
          (extractCrossing (repairRelation (sumModel (F.model n B.i) (F.model n B.l)) U)) :
            ℕ) : ℝ) ≤
        ((B.f.sourceDefect + B.g.sourceDefect +
          (B.g.targetDefect + B.f.targetDefect) : ℕ) : ℝ) +
          6 * ((U ∆ permutationGraph (sumModel (F.model n B.i) (F.model n B.l))
            (B.f.trans B.g).swapPerm).card : ℝ) := by
    exact_mod_cast hdistNat
  have hdsum :
      ((B.f.sourceDefect + B.g.sourceDefect +
          (B.g.targetDefect + B.f.targetDefect) : ℕ) : ℝ) <
        3 * η * F.scale n B.i := by
    push_cast
    exact arith_defect_sum hsT (card_mul_sourceDefect_lt_of_candidate B.hf)
      (card_mul_sourceDefect_lt_of_candidate B.hg)
      (card_mul_targetDefect_lt_of_candidate B.hg)
      (card_mul_targetDefect_lt_of_candidate B.hf)
      (by positivity) (by positivity) (by positivity) (by positivity) hmYr hη
  have hmXle : (F.scale n B.i : ℝ) ≤ (Fintype.card (F.model n B.i) : ℝ) := by
    have h : F.scale n B.i ≤ Fintype.card (F.model n B.i) := by omega
    exact_mod_cast h
  have hfinal := arith_distance hdistReal hdsum hE hηζ (by positivity) hmXle hζ0
  refine B.noImprove
    (extractCrossing (repairRelation (sumModel (F.model n B.i) (F.model n B.l)) U))
    ⟨hrep.1, ?_, ?_⟩
  · rw [twoSidedDisagreement_comm]
    exact hrep.2
  · rw [twoSidedDisagreement_comm]
    exact hfinal

end BadTriple

open Classical in
/-- **Improvement at fixed parameters.** -/
theorem eventually_improveCloseAt
    {Q : Finset K} {κ : ℝ} (hQ : IsKazhdanPair.{0, 0} K Q κ) (hQT : Q ⊆ T)
    (hone : (1 : K) ∈ T) (hκone : κ ≤ 1)
    {k : ℕ} {η δ ζ : ℝ} (hk : 0 < k) (hη : 0 < η) (hδ : 0 < δ)
    (hζ : ζ ≤ 1 / 100000) (hηζ : η < ζ) (hkη : (k : ℝ) ^ 2 * η < ζ)
    (hnumerical : 16 * (T.card : ℝ) ^ 4 *
        (16 * (1 - κ ^ 2 / (4 * T.card)) ^ (2 * k) * (T.card : ℝ)⁻¹ * η + δ) <
      (((1 : ℝ) / 3) * (((2 : ℝ) / 3) - (1 : ℝ) / 3) ^ 2) ^ 2 *
        (F.repairFactor * η) ^ 4) :
    ∃ N : ℕ, ∀ n ≥ N, F.ImproveCloseAt η (20000 * ζ) n := by
  classical
  by_contra hcontra
  have hbad : ∀ N : ℕ, ∃ n, N ≤ n ∧ Nonempty (F.BadTriple η (20000 * ζ) n) := by
    intro N
    by_contra hN
    exact hcontra ⟨N, fun n hn ↦
      F.improveCloseAt_of_not_nonempty fun hne ↦ hN ⟨n, hn, hne⟩⟩
  choose seq hseq hbadN using hbad
  have hηsmall : η ≤ 1 / 100000 := by linarith only [hζ, hηζ]
  let bad : ∀ N, F.BadTriple η (20000 * ζ) (seq N) := fun N ↦ Classical.choice (hbadN N)
  let modelX : ℕ → FiniteModel := fun N ↦ F.model (seq N) (bad N).i
  let modelZ : ℕ → FiniteModel := fun N ↦ F.model (seq N) (bad N).l
  let actX : ∀ N, K → Equiv.Perm (modelX N) := fun N ↦ F.act (seq N) (bad N).i
  let actZ : ∀ N, K → Equiv.Perm (modelZ N) := fun N ↦ F.act (seq N) (bad N).l
  have hposX : ∀ N, 0 < Fintype.card (modelX N) := by
    intro N
    obtain ⟨h1, h18, _, _, _⟩ := (bad N).sizes hηsmall hone
    show 0 < Fintype.card (F.model (seq N) (bad N).i)
    omega
  have hposZ : ∀ N, 0 < Fintype.card (modelZ N) := by
    intro N
    obtain ⟨h1, _, _, h17, _⟩ := (bad N).sizes hηsmall hone
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
  have ha : IsEpsilonGood (A.model N) (multiplicativeProductLabels A N T) η
      ((bad N).f.trans (bad N).g).swapPerm := by
    rw [hlabels]
    exact (bad N).swap_isEpsilonGood hη hηsmall hone
  have hb : IsEpsilonGood (A.model N) (multiplicativeProductLabels A N T) η 1 :=
    isEpsilonGood_one (A.model N) _ hη hcardPos
  obtain ⟨U, hUclose, hUboundary⟩ := hN₁ N hN1 hinj hcardPos ha hb
  rw [mul_one] at hUclose
  rw [hlabels] at hUboundary
  exact (bad N).exists_improvement hone hη hζ hηζ hkη U hUclose hUboundary

/-! ### The joint choice of threshold and distance -/

theorem one_div_lt_of_nat_gt {a : ℝ} (ha : 0 < a) {j : ℕ} (hj : 1 / a < j) :
    1 / (100000 * ((j : ℝ) + 1)) < a := by
  have hpos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hle : 1 / (100000 * ((j : ℝ) + 1)) ≤ 1 / ((j : ℝ) + 1) :=
    one_div_le_one_div_of_le hpos (by nlinarith only [hpos])
  have hlt : 1 / ((j : ℝ) + 1) < a := by
    rw [div_lt_iff₀ hpos]
    have h := (div_lt_iff₀ ha).1 hj
    nlinarith only [h, ha]
  linarith only [hle, hlt]

theorem one_div_antitone_nat {i j : ℕ} (hij : i ≤ j) :
    1 / (100000 * ((j : ℝ) + 1)) ≤ 1 / (100000 * ((i : ℝ) + 1)) := by
  apply one_div_le_one_div_of_le (by positivity)
  have h : (i : ℝ) ≤ j := by exact_mod_cast hij
  linarith only [h]

open Classical in
/-- **Joint threshold and distance.**  The threshold `h n` and the distance
factor `d n` tend to zero, `h` dominates the prescribed vanishing sequence `ρ`,
and improvement with that threshold and distance holds eventually. -/
theorem exists_joint_improvement
    {Q : Finset K} {κ : ℝ} (hQ : IsKazhdanPair.{0, 0} K Q κ) (hQT : Q ⊆ T)
    (hone : (1 : K) ∈ T) (hκone : κ ≤ 1)
    (ρ : ℕ → ℝ) (hρ : Tendsto ρ atTop (𝓝 0)) :
    ∃ (h d : ℕ → ℝ), (∀ n, 0 < h n) ∧ Tendsto h atTop (𝓝 0) ∧
      Tendsto d atTop (𝓝 0) ∧ (∀ᶠ n in atTop, ρ n ≤ h n) ∧
      ∃ N₀ : ℕ, ∀ n ≥ N₀, F.ImproveCloseAt (h n) (d n) n := by
  classical
  obtain ⟨hq0, hq1⟩ := kazhdanFactor_nonneg_lt_one hQ T hone hκone
  have hs : 0 < T.card := Finset.card_pos.mpr ⟨1, hone⟩
  have hp := F.repairFactor_pos hone
  have hlevel : ∀ j : ℕ, ∃ (k : ℕ) (η δ : ℝ), 0 < k ∧ 0 < η ∧ 0 < δ ∧
      η < 1 / (100000 * ((j : ℝ) + 1)) ∧
      (k : ℝ) ^ 2 * η < 1 / (100000 * ((j : ℝ) + 1)) ∧
      16 * (T.card : ℝ) ^ 4 *
          (16 * (1 - κ ^ 2 / (4 * T.card)) ^ (2 * k) * (T.card : ℝ)⁻¹ * η + δ) <
        (((1 : ℝ) / 3) * (((2 : ℝ) / 3) - (1 : ℝ) / 3) ^ 2) ^ 2 *
          (F.repairFactor * η) ^ 4 := by
    intro j
    exact exists_repairParameters hq0 hq1 T.card hs hp (by positivity)
  choose kf ηf δf hk hη hδ hηζ hkη hnum using hlevel
  have hζ : ∀ j : ℕ, 1 / (100000 * ((j : ℝ) + 1)) ≤ 1 / 100000 := by
    intro j
    apply one_div_le_one_div_of_le (by norm_num)
    have hj : (0 : ℝ) ≤ j := by positivity
    linarith only [hj]
  have hevent : ∀ j : ℕ, ∃ N : ℕ, ∀ n ≥ N,
      F.ImproveCloseAt (ηf j) (20000 * (1 / (100000 * ((j : ℝ) + 1)))) n := by
    intro j
    exact F.eventually_improveCloseAt hQ hQT hone hκone (hk j) (hη j) (hδ j) (hζ j)
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
    exact ((hηζ (J n)).trans_le hmono).trans (one_div_lt_of_nat_gt ha hj)
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
    exact hNf (J n) n ((hNM (J n)).trans (hJspec n hn))

end ComponentFamily

end CentralizerNormalizationImprove
end GroupApproximation
