import GroupApproximation.GGT.HullSCLemma49QuadrangleShadow

/-!
# Stable translation makes a geodesic power boundary uniform

Hull's auxiliary lemma `aaqg` uses Bowditch's positive lower bound on stable
translation lengths to treat shortest loxodromic representatives whose word
length is bounded.  This file proves the word-level part of that argument.

If a geodesic period has length at most `L`, its complete-period vertices are
the orbit points `g^q`.  A lower bound `d` for the stable translation of `g`
therefore gives linear progress between complete-period vertices.  Moving the
two endpoints to the nearest complete periods costs at most two period
lengths.  If `L ≤ d * M`, every finite power word is consequently an
`(M, 4*L)` quasi-geodesic chain.

The constants are deliberately separated from the acylindricity argument.
Bowditch Lemma 2.2 chooses `d`; Archimedean rounding then chooses the positive
natural `M`.  No diagram or small-cancellation hypothesis occurs here.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric

universe u w

/-! ## Complete-period vertices -/

/-- Boundary powers add by literal word concatenation. -/
theorem lemma49BoundaryPower_add {Alpha : Type*} (word : List Alpha)
    (a b : ℕ) :
    lemma49BoundaryPower word (a + b) =
      lemma49BoundaryPower word a ++ lemma49BoundaryPower word b := by
  induction a with
  | zero => simp [lemma49BoundaryPower]
  | succ a ih =>
      rw [Nat.succ_add, lemma49BoundaryPower, lemma49BoundaryPower, ih,
        List.append_assoc]

/-- At a complete-period index, the power-boundary vertex is the
corresponding group power. -/
theorem vertex_lemma49BoundaryPower_mul_length
    {G : Type u} [Group G] {Lambda : Type w}
    {word : List (GGT.RelLetter G Lambda)} {g : G}
    (hvalue : GGT.RelLetter.listVal word = g)
    {n q : ℕ} (hq : q ≤ n) :
    GGT.OsinComponents.vertex 1 (lemma49BoundaryPower word n)
        (q * word.length) = g ^ q := by
  have hn : n = q + (n - q) := (Nat.add_sub_of_le hq).symm
  have hsplit : lemma49BoundaryPower word n =
      lemma49BoundaryPower word q ++ lemma49BoundaryPower word (n - q) := by
    rw [hn, lemma49BoundaryPower_add]
  have hlength : (lemma49BoundaryPower word q).length = q * word.length :=
    lemma49BoundaryPower_length word q
  rw [hsplit, ← hlength,
    GGT.OsinComponents.vertex_append_of_le _ _ _ _ le_rfl,
    GGT.OsinComponents.vertex_length,
    listVal_lemma49BoundaryPower, hvalue, one_mul]

/-! ## Arithmetic around the nearest complete periods -/

/-- If there is no complete period strictly between two indices, their gap
is less than two periods. -/
theorem sub_lt_two_mul_of_div_add_one_gt_div
    {i j period : ℕ} (hperiod : 0 < period) (hij : i ≤ j)
    (hdiv : j / period < i / period + 1) :
    j - i < 2 * period := by
  have hiMod : i % period < period := Nat.mod_lt i hperiod
  have hjMod : j % period < period := Nat.mod_lt j hperiod
  have hiDecomp := Nat.div_add_mod i period
  have hjDecomp := Nat.div_add_mod j period
  nlinarith

/-- When complete periods do occur between the indices, the total gap is at
most their orbit-index gap plus the two endpoint periods. -/
theorem sub_le_period_gap_add_two
    {i j period : ℕ} (hperiod : 0 < period) (hij : i ≤ j)
    (hdiv : i / period + 1 ≤ j / period) :
    j - i ≤ (j / period - (i / period + 1) + 2) * period := by
  have hiMod : i % period < period := Nat.mod_lt i hperiod
  have hjMod : j % period < period := Nat.mod_lt j hperiod
  have hiDecomp := Nat.div_add_mod i period
  have hjDecomp := Nat.div_add_mod j period
  nlinarith

/-! ## The stable-translation power chain -/

/-- A stable-translation lower bound makes every finite power of a bounded
geodesic period one uniform quasi-geodesic chain.  This is Hull's short-word
case in auxiliary lemma `aaqg`, stated with an integral multiplicative
constant for direct use by the Morse shadow theorem. -/
theorem isQuasiGeodesicChainAt_power_of_stableTranslation
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) {g : G}
    {word : List (GGT.RelLetter G Lambda)}
    (hword : GGT.OsinComponents.IsGeodesicWord D 1 g word)
    {n L M : ℕ} (hwordPos : 0 < word.length)
    (hlength : word.length ≤ L) (hM : 0 < M)
    {d : ℝ} (hd : 0 < d)
    (hdStable : d ≤ stableTranslation g (Cayley.base D.alphabet))
    (hdL : d ≤ L) (hLM : (L : ℝ) ≤ d * M) :
    GGT.IsQuasiGeodesicChainAt D.alphabet.carrier M (4 * L)
      (fun i => GGT.OsinComponents.vertex 1
        (lemma49BoundaryPower word n) i)
      (lemma49BoundaryPower word n).length := by
  let power := lemma49BoundaryPower word n
  have hpowerLetters : ∀ a ∈ power, D.IsLetter a := by
    dsimp [power]
    exact isAdmissible_lemma49BoundaryPower hword.1 n
  have hvalue : GGT.RelLetter.listVal word = g := by
    simpa using hword.2.1
  have hMReal : (0 : ℝ) < (M : ℝ) := by
    exact_mod_cast hM
  have hdNonneg : 0 ≤ d := le_of_lt hd
  intro i j hij hj
  have hupper : wordDist D.alphabet.carrier
      (GGT.OsinComponents.vertex 1 power i)
      (GGT.OsinComponents.vertex 1 power j) ≤ j - i :=
    GGT.OsinComponents.wordDist_vertex_le D hpowerLetters hij hj
  refine ⟨?_, hupper⟩
  let qLeft := i / word.length + 1
  let qRight := j / word.length
  by_cases hcomplete : qLeft ≤ qRight
  · let leftIndex := qLeft * word.length
    let rightIndex := qRight * word.length
    have hleftIndex : i ≤ leftIndex := by
      dsimp [leftIndex, qLeft]
      have hiMod : i % word.length < word.length :=
        Nat.mod_lt i hwordPos
      have hiDecomp := Nat.div_add_mod i word.length
      nlinarith
    have hrightIndex : rightIndex ≤ j := by
      dsimp [rightIndex, qRight]
      exact Nat.div_mul_le_self j word.length
    have hleftFit : leftIndex ≤ power.length := by
      exact le_trans hrightIndex (le_trans hij hj)
    have hrightFit : rightIndex ≤ power.length :=
      le_trans hrightIndex hj
    have hqLeft : qLeft ≤ n := by
      dsimp [leftIndex, power] at hleftFit
      rw [lemma49BoundaryPower_length] at hleftFit
      exact Nat.le_of_mul_le_mul_right hleftFit hwordPos
    have hqRight : qRight ≤ n := by
      dsimp [rightIndex, power] at hrightFit
      rw [lemma49BoundaryPower_length] at hrightFit
      exact Nat.le_of_mul_le_mul_right hrightFit hwordPos
    have hleftClose : wordDist D.alphabet.carrier
        (GGT.OsinComponents.vertex 1 power i)
        (GGT.OsinComponents.vertex 1 power leftIndex) ≤ word.length := by
      have hraw := GGT.OsinComponents.wordDist_vertex_le D hpowerLetters
        hleftIndex hleftFit
      have hiMod : i % word.length < word.length :=
        Nat.mod_lt i hwordPos
      have hiDecomp := Nat.div_add_mod i word.length
      dsimp [leftIndex, qLeft] at hraw
      omega
    have hrightClose : wordDist D.alphabet.carrier
        (GGT.OsinComponents.vertex 1 power rightIndex)
        (GGT.OsinComponents.vertex 1 power j) ≤ word.length := by
      have hraw := GGT.OsinComponents.wordDist_vertex_le D hpowerLetters
        hrightIndex hj
      have hjMod : j % word.length < word.length :=
        Nat.mod_lt j hwordPos
      have hjDecomp := Nat.div_add_mod j word.length
      dsimp [rightIndex, qRight] at hraw
      omega
    have hleftVertex : GGT.OsinComponents.vertex 1 power leftIndex =
        g ^ qLeft := by
      dsimp [power, leftIndex]
      exact vertex_lemma49BoundaryPower_mul_length hvalue hqLeft
    have hrightVertex : GGT.OsinComponents.vertex 1 power rightIndex =
        g ^ qRight := by
      dsimp [power, rightIndex]
      exact vertex_lemma49BoundaryPower_mul_length hvalue hqRight
    have horbit := (orbit_quasiIsometricEmbedding
      (isIsometricAction_cayley D.alphabet) g (Cayley.base D.alphabet)
      (qLeft : ℤ) (qRight : ℤ)).1
    have hqDiff : ((qRight : ℤ) - (qLeft : ℤ)) =
        (qRight - qLeft : ℕ) := by
      omega
    have horbitLower : d * (qRight - qLeft : ℕ) ≤
        (wordDist D.alphabet.carrier (g ^ qLeft) (g ^ qRight) : ℝ) := by
      simp only [hqDiff, Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg _),
        zpow_natCast, Cayley.dist_eq, Cayley.val_smul, Cayley.val_base,
        mul_one] at horbit
      have hscaled := mul_le_mul_of_nonneg_right hdStable
        (Nat.cast_nonneg (qRight - qLeft))
      exact le_trans hscaled horbit
    have hcentralNat : wordDist D.alphabet.carrier
        (g ^ qLeft) (g ^ qRight) ≤
        word.length + wordDist D.alphabet.carrier
          (GGT.OsinComponents.vertex 1 power i)
          (GGT.OsinComponents.vertex 1 power j) + word.length := by
      rw [← hleftVertex, ← hrightVertex]
      have hleftComm := wordDist_comm D.alphabet.symmetricGenerating
        (GGT.OsinComponents.vertex 1 power leftIndex)
        (GGT.OsinComponents.vertex 1 power i)
      have hrightComm := wordDist_comm D.alphabet.symmetricGenerating
        (GGT.OsinComponents.vertex 1 power j)
        (GGT.OsinComponents.vertex 1 power rightIndex)
      have htri₁ := wordDist_triangle D.alphabet.symmetricGenerating
        (GGT.OsinComponents.vertex 1 power leftIndex)
        (GGT.OsinComponents.vertex 1 power i)
        (GGT.OsinComponents.vertex 1 power j)
      have htri₂ := wordDist_triangle D.alphabet.symmetricGenerating
        (GGT.OsinComponents.vertex 1 power leftIndex)
        (GGT.OsinComponents.vertex 1 power j)
        (GGT.OsinComponents.vertex 1 power rightIndex)
      omega
    have hcentralReal :
        (wordDist D.alphabet.carrier (g ^ qLeft) (g ^ qRight) : ℝ) ≤
          (word.length : ℝ) +
            (wordDist D.alphabet.carrier
              (GGT.OsinComponents.vertex 1 power i)
              (GGT.OsinComponents.vertex 1 power j) : ℝ) +
            (word.length : ℝ) := by
      exact_mod_cast hcentralNat
    have hgapNat : j - i ≤
        (qRight - qLeft + 2) * word.length := by
      exact sub_le_period_gap_add_two hwordPos hij hcomplete
    have hgapReal : ((j - i : ℕ) : ℝ) ≤
        ((qRight - qLeft + 2 : ℕ) : ℝ) * (word.length : ℝ) := by
      exact_mod_cast hgapNat
    have hwordLM : (word.length : ℝ) ≤ d * (M : ℝ) :=
      le_trans (by exact_mod_cast hlength) hLM
    have hgapScaled : ((j - i : ℕ) : ℝ) / (M : ℝ) ≤
        d * ((qRight - qLeft : ℕ) : ℝ) + 2 * d := by
      rw [div_le_iff₀ hMReal]
      have hmul := mul_le_mul_of_nonneg_left hwordLM
        (Nat.cast_nonneg (qRight - qLeft + 2))
      push_cast at hmul
      nlinarith
    have hwordL : (word.length : ℝ) ≤ (L : ℝ) := by
      exact_mod_cast hlength
    push_cast
    linarith
  · have hqReverse : qRight < qLeft := by omega
    have hgapNat : j - i < 2 * word.length := by
      exact sub_lt_two_mul_of_div_add_one_gt_div hwordPos hij hqReverse
    have hgapL : ((j - i : ℕ) : ℝ) < 2 * (L : ℝ) := by
      have hgapReal : ((j - i : ℕ) : ℝ) < 2 * (word.length : ℝ) := by
        exact_mod_cast hgapNat
      have hwordL : (word.length : ℝ) ≤ (L : ℝ) := by
        exact_mod_cast hlength
      linarith
    have hdiv : ((j - i : ℕ) : ℝ) / (M : ℝ) ≤
        ((j - i : ℕ) : ℝ) := by
      rw [div_le_iff₀ hMReal]
      have hMOne : (1 : ℝ) ≤ (M : ℝ) := by
        exact_mod_cast hM
      have hgapNonneg : (0 : ℝ) ≤ ((j - i : ℕ) : ℝ) := by positivity
      nlinarith
    have hdistNonneg : (0 : ℝ) ≤
        (wordDist D.alphabet.carrier
          (GGT.OsinComponents.vertex 1 power i)
          (GGT.OsinComponents.vertex 1 power j) : ℝ) := by positivity
    push_cast
    linarith

/-! ## Numerical check -/

/-- The parameter inequalities used by the stable-power theorem have a
nonempty integral model, including a multiplicative constant larger than the
long-period value `4`. -/
theorem stablePowerChain_parameters_model :
    (3 : ℝ) ≤ (1 / 2 : ℝ) * 6 ∧ 0 < (6 : ℕ) ∧
      (1 / 2 : ℝ) ≤ 3 := by
  norm_num

end HullSC
end GroupApproximation
