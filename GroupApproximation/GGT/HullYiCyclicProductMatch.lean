import GroupApproximation.GGT.HullYiCyclicProductWord
import GroupApproximation.GGT.HullSCRelatorSeparationBall
import GroupApproximation.GGT.ElementaryPositiveIndex
import GroupApproximation.GGT.HullYiElementaryClosureFamily

/-!
# DGO component matches for Hull's cyclic products

Hull's proof of Lemma 5.6 applies Dahmani--Guirardel--Osin Lemma 4.21(b)
twice.  Applied to a cyclic word and its reverse, two matched components rule
out conjugation to the inverse power because the peripheral indices advance in
one word and retreat in the other.  Applied to two forward copies, a full
cycle of matched components gives the connector equations used in Hull's
calculation.

This file proves both steps at the exact depth threshold supplied by Lemma
4.21(b).  The first theorem gives orientation preservation.  The second
combines it with `exists_depth_hasConsecutiveComponentMatchData_of_positiveNormalizer`
and gives the complete connector data.  The letters are chosen after the
threshold, in the same quantifier order as Hull's proof.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.GGT
open GroupApproximation.GGT.Elementary
open GroupApproximation.GGT.OsinComponents
open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

variable {G : Type u} [Group G]

/-- An element of the elementary closure preserves the orientation of some
positive power.  This is the conclusion obtained from the `123123...` versus
`321321...` argument in Hull's Lemmas 5.4 and 5.6. -/
def HasPositivePowerNormalizer (h : G) : Prop :=
  ∀ t : G, t ∈ elementaryClosure h →
    ∃ q : ℕ, 0 < q ∧ t * h ^ q * t⁻¹ = h ^ q

/-- The trivial product satisfies the positive-normalizer condition directly.
This tests the definition when every component word is empty. -/
theorem hasPositivePowerNormalizer_one :
    HasPositivePowerNormalizer (1 : G) := by
  intro t _ht
  refine ⟨1, by norm_num, ?_⟩
  simp

/-- The positive-normalizer condition has the intended cyclic model.  If the
elementary closure is the cyclic subgroup itself, every member commutes with
the first positive power. -/
theorem hasPositivePowerNormalizer_of_elementaryClosure_eq_zpowers {h : G}
    (hcyc : elementaryClosure h = Subgroup.zpowers h) :
    HasPositivePowerNormalizer h := by
  intro t ht
  rw [hcyc] at ht
  obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
  refine ⟨1, by norm_num, ?_⟩
  simp only [pow_one]
  group

/-- The positive-power normalizer condition is exactly the orientation-purity
conclusion Hull needs.  Apply it to `t⁻¹`: the resulting equation is the
inverse-conjugation equation defining `E⁺(h)`. -/
theorem elementaryClosure_eq_positive_of_hasPositivePowerNormalizer {h : G}
    (hnormal : HasPositivePowerNormalizer h) :
    (elementaryClosure h : Set G) = positiveElementaryClosure h := by
  ext t
  constructor
  · intro ht
    have htinv : t⁻¹ ∈ elementaryClosure h := (elementaryClosure h).inv_mem ht
    obtain ⟨q, hq, hconj⟩ := hnormal t⁻¹ htinv
    refine ⟨(q : ℤ), by exact_mod_cast hq.ne', ?_⟩
    simpa only [inv_inv, zpow_natCast] using hconj
  · intro ht
    exact positiveElementaryClosure_le_elementaryClosure h ht

/-- Orientation purity plus DGO Corollary 6.6 gives Hull's centralizer power,
with no global coarse-translation input.  The finite transversal follows from
the Hull generating set's hyperbolic acylindrical Cayley action. -/
theorem exists_elementaryClosure_eq_centralizer_pow_of_hasPositivePowerNormalizer
    (A : HullGeneratingSet G) {h : G}
    (hlox : IsLoxodromic h (Cayley.base A.alphabet))
    (hnormal : HasPositivePowerNormalizer h) :
    ∃ r : ℕ, 0 < r ∧ (elementaryClosure h : Set G) =
      {t : G | Commute t (h ^ (r : ℤ))} := by
  have hfin : ElementaryClosureFiniteTransversal h :=
    elementaryClosureFiniteTransversal_hullGeneratingSet A hlox
  obtain ⟨r, hr, hcentral⟩ :=
    exists_positiveElementaryClosure_eq_centralizer_pow
      (isIsometricAction_cayley A.alphabet) hlox hfin
  exact ⟨r, hr,
    (elementaryClosure_eq_positive_of_hasPositivePowerNormalizer hnormal).trans
      hcentral⟩

/-- **Hull's inverse-orientation exclusion from DGO Lemma 4.21(b).**

For a cyclic word on at least three peripheral factors, Lemma 4.21(b) chooses
a depth `C`.  If every cyclic letter lies outside its `C`-ball, every element
of the elementary closure of the product conjugates a positive power of the
product to itself.

The only alternative supplied by the elementary-closure normalization is
conjugation to the inverse power.  In that case the forward cyclic word and
its reverse are oriented-close after passing to a multiple.  Two consecutive
matches then make one peripheral index equal to both its cyclic successor and
its cyclic predecessor, which is impossible for a cycle of length at least
three. -/
theorem exists_depth_hasPositivePowerNormalizer_cyclicProduct_of_dgoLemma421b
    (h421b : DGOLemma421b.{u, 0}) (A : Alphabet G)
    (f : Fin (k + 1) → G) (hk : 2 ≤ k)
    (hhyp : ∃ δ : ℝ, IsHyperbolicSpace δ
      (Cayley (coneOffFamily A (fun i ↦ elementaryClosure (f i))).alphabet))
    : ∃ C : ℕ, ∀ (a : Fin (k + 1) → G),
      (∀ i, a i ∈ elementaryClosure (f i)) →
      (∀ i, a i ∉
        (coneOffFamily A (fun j ↦ elementaryClosure (f j))).relBall i C) →
      IsLoxodromic (orderedFinProduct a) (Cayley.base A) →
      HasPositivePowerNormalizer (orderedFinProduct a) := by
  let D : RelGenSet G (Fin (k + 1)) :=
    coneOffFamily A (fun i ↦ elementaryClosure (f i))
  obtain ⟨C, hraw⟩ := h421b G (Fin (k + 1)) D hhyp
  refine ⟨C, ?_⟩
  intro a ha hdeep hlox t ht
  obtain ⟨q, hq, hpos | hneg⟩ :=
    exists_conj_positive_zpow_eq_or_of_mem_elementaryClosure
      (isIsometricAction_cayley A) hlox ht
  · refine ⟨q, hq, ?_⟩
    simpa [zpow_natCast] using hpos
  · exfalso
    let K : ℕ := 2
    let eps : ℝ := (wordDist D.alphabet.carrier 1 t : ℝ) + 1
    have heps : 0 < eps := by
      dsimp [eps]
      positivity
    have hK : 0 < K := by simp [K]
    obtain ⟨R, -, hmatch⟩ := hraw eps K heps hK
    let N := q * R
    let w := cyclicPeripheralPowerWord a N
    have hcycle : 0 < k + 1 := by omega
    have hlength : R ≤ N * (k + 1) := by
      dsimp [N]
      exact (Nat.le_mul_of_pos_left R hq).trans
        (Nat.le_mul_of_pos_right (q * R) hcycle)
    have hnegNat :
        t * orderedFinProduct a ^ q * t⁻¹ =
          (orderedFinProduct a ^ q)⁻¹ := by
      simpa [zpow_natCast, zpow_neg] using hneg
    have hnegN :
        t * orderedFinProduct a ^ N * t⁻¹ =
          (orderedFinProduct a ^ N)⁻¹ := by
      dsimp [N]
      calc
        t * orderedFinProduct a ^ (q * R) * t⁻¹ =
            (t * orderedFinProduct a ^ q * t⁻¹) ^ R := by
              rw [pow_mul, conj_pow]
        _ = ((orderedFinProduct a ^ q)⁻¹) ^ R := by rw [hnegNat]
        _ = (orderedFinProduct a ^ (q * R))⁻¹ := by
          rw [pow_mul, inv_pow]
    have hreverseN :
        t * (orderedFinProduct a ^ N)⁻¹ =
          orderedFinProduct a ^ N * t := by
      have hconjInv :
          t * (orderedFinProduct a ^ N)⁻¹ * t⁻¹ =
            orderedFinProduct a ^ N := by
        calc
          t * (orderedFinProduct a ^ N)⁻¹ * t⁻¹ =
              (t * orderedFinProduct a ^ N * t⁻¹)⁻¹ := by group
          _ = ((orderedFinProduct a ^ N)⁻¹)⁻¹ := by rw [hnegN]
          _ = orderedFinProduct a ^ N := inv_inv _
      calc
        t * (orderedFinProduct a ^ N)⁻¹ =
            (t * (orderedFinProduct a ^ N)⁻¹ * t⁻¹) * t := by group
        _ = orderedFinProduct a ^ N * t := by rw [hconjInv]
    have hletter : ∀ c ∈ w, D.IsLetter c := by
      dsimp [w]
      apply isLetter_of_mem_blockWord D (Fin.last k)
      · exact isLetter_indexedPeripheralWord D
          (fun i ↦ i.castSucc) (fun i ↦ a i.castSucc)
          (fun i ↦ ha i.castSucc)
      · exact ha (Fin.last k)
    have hletterRev : ∀ c ∈ revWord w, D.IsLetter c :=
      isLetter_of_mem_revWord D A.symmetricGenerating.inv_mem hletter
    have hW1 : WWord.IsWOne w := by
      dsimp [w]
      exact isWOne_blockWord_finPeripheralWord a N
    have hW2 : WWord.IsWTwo D C w := by
      dsimp [w]
      exact isWTwo_blockWord_finPeripheralWord D a hdeep N
    have hW3 : WWord.IsWThree D w := by
      dsimp [w]
      exact isWThree_blockWord_finPeripheralWord D (by omega) a N
    have hW1Rev : WWord.IsWOne (revWord w) := isWOne_revWord hW1
    have hW2Rev : WWord.IsWTwo D C (revWord w) :=
      isWTwo_revWord D A.symmetricGenerating.inv_mem hW2
    have hW3Rev : WWord.IsWThree D (revWord w) := isWThree_revWord D hW3
    have hstart : (wordDist D.alphabet.carrier 1 t : ℝ) ≤ eps := by
      dsimp [eps]
      norm_num
    have hend :
        (wordDist D.alphabet.carrier
          (vertex 1 w w.length)
          (vertex t (revWord w) (revWord w).length) : ℝ) ≤ eps := by
      simp only [vertex_length, listVal_revWord]
      dsimp [w]
      rw [listVal_cyclicPeripheralPowerWord, one_mul, hreverseN]
      have hdist := wordDist_left_invariant D.alphabet.carrier
        (orderedFinProduct a ^ N)⁻¹ (orderedFinProduct a ^ N)
        (orderedFinProduct a ^ N * t)
      have hsimp :
          (orderedFinProduct a ^ N)⁻¹ *
              (orderedFinProduct a ^ N * t) = t := by group
      rw [inv_mul_cancel, hsimp] at hdist
      calc
        (wordDist D.alphabet.carrier (orderedFinProduct a ^ N)
            (orderedFinProduct a ^ N * t) : ℝ) =
            (wordDist D.alphabet.carrier 1 t : ℝ) := by
              exact_mod_cast hdist.symm
        _ ≤ eps := hstart
    obtain ⟨ip, kp, iq, kq, lam, hcomp, hcompRev, hstep, hstepRev, -⟩ :=
      hmatch 1 t w (revWord w) hletter hletterRev
        hW1 hW2 hW3 hW1Rev hW2Rev hW3Rev
        (by simpa [w] using hlength) hstart hend
    have hsucc := cyclicSucc_componentIndex_of_consecutiveMatches
      D (by omega) a N K ip kp lam hcomp hstep 0 (by simp [K])
    have hpred := cyclicPred_componentIndex_of_consecutiveMatches_rev
      D (by omega) a N K iq kq lam hcompRev hstepRev 0 (by simp [K])
    exact cyclicSucc_ne_cyclicPred (by omega) (lam 0) (hsucc.symm.trans hpred)

/-- **The complete forward-match data at a single depth.**

The inverse-orientation call and the forward self-match may choose different
depth thresholds.  Taking their maximum makes both applications valid.  The
result is the connector array and prefix equation used by Hull's Lemma 5.6,
stopping before the later cyclicity conclusion. -/
theorem exists_depth_hasConsecutiveComponentMatchData_of_dgoLemma421b
    (h421b : DGOLemma421b.{u, 0}) (A : Alphabet G)
    (f : Fin (k + 1) → G) (hk : 2 ≤ k)
    (hhyp : ∃ δ : ℝ, IsHyperbolicSpace δ
      (Cayley (coneOffFamily A (fun i ↦ elementaryClosure (f i))).alphabet)) :
    ∃ C : ℕ, ∀ (a : Fin (k + 1) → G),
      (∀ i, a i ∈ elementaryClosure (f i)) →
      (∀ i, a i ∉
        (coneOffFamily A (fun j ↦ elementaryClosure (f j))).relBall i C) →
      IsLoxodromic (orderedFinProduct a) (Cayley.base A) →
      ∀ t : G, t ∈ elementaryClosure (orderedFinProduct a) →
      ∃ (l m : ℤ) (p : G) (c : Fin (k + 2) → G),
        (∀ i : Fin (k + 1),
          c i.castSucc ∈ elementaryClosure (f i)) ∧
        (∀ i : Fin (k + 1),
          c i.succ = (a i)⁻¹ * c i.castSucc * a i) ∧
        t = orderedFinProduct a ^ l * p * c 0 * p⁻¹ *
          orderedFinProduct a ^ (-m) := by
  obtain ⟨Corient, horient⟩ :=
    exists_depth_hasPositivePowerNormalizer_cyclicProduct_of_dgoLemma421b
      h421b A f hk hhyp
  obtain ⟨Cmatch, hmatch⟩ :=
    exists_depth_hasConsecutiveComponentMatchData_of_positiveNormalizer
      h421b A f (by omega) hhyp
  refine ⟨max Corient Cmatch, ?_⟩
  intro a ha hdeep hlox t ht
  have hdeepOrient : ∀ i, a i ∉
      (coneOffFamily A (fun j ↦ elementaryClosure (f j))).relBall i Corient := by
    intro i
    exact notMem_relBall_of_le (Nat.le_max_left _ _) (hdeep i)
  have hdeepMatch : ∀ i, a i ∉
      (coneOffFamily A (fun j ↦ elementaryClosure (f j))).relBall i Cmatch := by
    intro i
    exact notMem_relBall_of_le (Nat.le_max_right _ _) (hdeep i)
  have horientA : HasPositivePowerNormalizer (orderedFinProduct a) := by
    exact horient a ha hdeepOrient hlox
  obtain ⟨q, hq, hnormalize⟩ := horientA t ht
  exact hmatch a ha hdeepMatch t q hq hnormalize

end HullSC
end GroupApproximation
