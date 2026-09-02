import GroupApproximation.GGT.HullYiCyclicProductMatch
import GroupApproximation.GGT.DGOLemma421Statement

/-!
# Pairwise non-commensurability of Hull's cyclic products

This is the second use of DGO Lemma 4.21(b) in Hull's Lemma 5.6.  Products in
the candidate family have a common prefix and differ only in their final deep
peripheral letter.  A same-orientation conjugacy of nonzero powers gives one
full forward component match.  Connector propagation makes the connector at
the final component trivial, so the terminal connector is exactly the ratio
of the two final letters, contrary to its exclusion from the first peripheral
subgroup.  Opposite orientations are excluded by the successor/predecessor
index argument.

The depth constant is existentially outside the letters.  Thus callers choose
the DGO constant before choosing the final powers, preserving Hull's printed
quantifier order.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.GGT
open GroupApproximation.GGT.Elementary
open GroupApproximation.GGT.OsinComponents
open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v

variable {G : Type u} [Group G]

/-- Every equality between conjugate nonzero integer powers has a positive
normal form, with the two positive powers either equal or inverse. -/
theorem exists_positive_conjugatePower_eq_or_inv {a b t : G} {p q : ℤ}
    (hp : p ≠ 0) (hq : q ≠ 0)
    (heq : t * a ^ p * t⁻¹ = b ^ q) :
    ∃ n m : ℕ, 0 < n ∧ 0 < m ∧
      (t * a ^ n * t⁻¹ = b ^ m ∨
        t * a ^ n * t⁻¹ = (b ^ m)⁻¹) := by
  let n := p.natAbs
  let m := q.natAbs
  have hn : 0 < n := Int.natAbs_pos.mpr hp
  have hm : 0 < m := Int.natAbs_pos.mpr hq
  refine ⟨n, m, hn, hm, ?_⟩
  rcases Int.natAbs_eq p with hpPos | hpNeg
  · rcases Int.natAbs_eq q with hqPos | hqNeg
    · left
      calc
        t * a ^ n * t⁻¹ = t * a ^ p * t⁻¹ := by
          rw [hpPos, zpow_natCast]
        _ = b ^ q := heq
        _ = b ^ m := by rw [hqPos, zpow_natCast]
    · right
      calc
        t * a ^ n * t⁻¹ = t * a ^ p * t⁻¹ := by
          rw [hpPos, zpow_natCast]
        _ = b ^ q := heq
        _ = (b ^ m)⁻¹ := by rw [hqNeg, zpow_neg, zpow_natCast]
  · rcases Int.natAbs_eq q with hqPos | hqNeg
    · right
      have heq' : t * a ^ (-(n : ℤ)) * t⁻¹ = b ^ m := by
        calc
          t * a ^ (-(n : ℤ)) * t⁻¹ = t * a ^ p * t⁻¹ := by
            rw [hpNeg]
          _ = b ^ q := heq
          _ = b ^ m := by rw [hqPos, zpow_natCast]
      calc
        t * a ^ n * t⁻¹ =
            (t * a ^ (-(n : ℤ)) * t⁻¹)⁻¹ := by
              rw [zpow_neg, zpow_natCast]
              group
        _ = (b ^ m)⁻¹ := by rw [heq']
    · left
      have heq' : t * a ^ (-(n : ℤ)) * t⁻¹ = b ^ (-(m : ℤ)) := by
        calc
          t * a ^ (-(n : ℤ)) * t⁻¹ = t * a ^ p * t⁻¹ := by
            rw [hpNeg]
          _ = b ^ q := heq
          _ = b ^ (-(m : ℤ)) := by rw [hqNeg]
      calc
        t * a ^ n * t⁻¹ =
            (t * a ^ (-(n : ℤ)) * t⁻¹)⁻¹ := by
              rw [zpow_neg, zpow_natCast]
              group
        _ = (b ^ (-(m : ℤ)))⁻¹ := by rw [heq']
        _ = b ^ m := by rw [zpow_neg, zpow_natCast, inv_inv]

/-- **DGO 4.21(b) makes a common-prefix cyclic-product family pairwise
non-commensurable.**

The terminal-ratio premise is deliberately the exact local fact used after
the forward match.  The selection theorem obtains it from pairwise
non-commensurability of the detector family and distinct nonzero powers in the
last peripheral subgroup. -/
theorem exists_depth_pairwiseNonCommensurable_cyclicProducts_of_dgoLemma421b
    (h421b : DGOLemma421b.{u, 0}) (A : Alphabet G)
    (f : Fin (k + 1) → G) (hk : 2 ≤ k)
    (hhyp : ∃ δ : ℝ, IsHyperbolicSpace δ
      (Cayley (coneOffFamily A (fun i ↦ elementaryClosure (f i))).alphabet)) :
    ∃ C : ℕ, ∀ {ι : Type v} (a : ι → Fin (k + 1) → G),
      (∀ j i, a j i ∈ elementaryClosure (f i)) →
      (∀ j i, a j i ∉
        (coneOffFamily A (fun r ↦ elementaryClosure (f r))).relBall i C) →
      (∀ j, IsLoxodromic (orderedFinProduct (a j)) (Cayley.base A)) →
      (∀ j l (i : Fin k), a j i.castSucc = a l i.castSucc) →
      (∀ j (i : Fin k),
        (elementaryClosure (f i.castSucc) : Set G) =
          {x : G | Commute x (a j i.castSucc)}) →
      (∀ x : G, (∀ i, x ∈ elementaryClosure (f i)) → x = 1) →
      (∀ j l, j ≠ l →
        (a j (Fin.last k))⁻¹ * a l (Fin.last k) ∉
          elementaryClosure (f 0)) →
      PairwiseNonCommensurable (fun j ↦ orderedFinProduct (a j)) := by
  let D : RelGenSet G (Fin (k + 1)) :=
    coneOffFamily A (fun i ↦ elementaryClosure (f i))
  obtain ⟨C, hraw⟩ := h421b G (Fin (k + 1)) D hhyp
    A.symmetricGenerating.inv_mem
  refine ⟨C, ?_⟩
  intro ι a ha hdeep hlox hcommon hcentral hinter hterminal
    j l hjl p q hp hq t heq
  obtain ⟨n, m, hn, hm, hsame | hopp⟩ :=
    exists_positive_conjugatePower_eq_or_inv hp hq heq
  · let K := 2 * (k + 1) + 1
    let eps : ℝ := (wordDist D.alphabet.carrier 1 t : ℝ) + 1
    have heps : 0 < eps := by
      dsimp [eps]
      positivity
    have hK : 0 < K := by simp [K]
    obtain ⟨R, -, hmatch⟩ := hraw eps K heps hK
    let N := n * R
    let M := m * R
    let wj := cyclicPeripheralPowerWord (a j) N
    let wl := cyclicPeripheralPowerWord (a l) M
    have hcycle : 0 < k + 1 := by omega
    have hlength : R ≤ M * (k + 1) := by
      dsimp [M]
      exact (Nat.le_mul_of_pos_left R hm).trans
        (Nat.le_mul_of_pos_right (m * R) hcycle)
    have hsameR :
        t * orderedFinProduct (a j) ^ N * t⁻¹ =
          orderedFinProduct (a l) ^ M := by
      dsimp [N, M]
      calc
        t * orderedFinProduct (a j) ^ (n * R) * t⁻¹ =
            (t * orderedFinProduct (a j) ^ n * t⁻¹) ^ R := by
              rw [pow_mul, conj_pow]
        _ = (orderedFinProduct (a l) ^ m) ^ R := by rw [hsame]
        _ = orderedFinProduct (a l) ^ (m * R) := by rw [pow_mul]
    have hcommuteR :
        t * orderedFinProduct (a j) ^ N =
          orderedFinProduct (a l) ^ M * t := by
      calc
        t * orderedFinProduct (a j) ^ N =
            (t * orderedFinProduct (a j) ^ N * t⁻¹) * t := by group
        _ = orderedFinProduct (a l) ^ M * t := by rw [hsameR]
    have hletterJ : ∀ c ∈ wj, D.IsLetter c := by
      dsimp [wj]
      apply isLetter_of_mem_blockWord D (Fin.last k)
      · exact isLetter_indexedPeripheralWord D
          (fun i ↦ i.castSucc) (fun i ↦ a j i.castSucc)
          (fun i ↦ ha j i.castSucc)
      · exact ha j (Fin.last k)
    have hletterL : ∀ c ∈ wl, D.IsLetter c := by
      dsimp [wl]
      apply isLetter_of_mem_blockWord D (Fin.last k)
      · exact isLetter_indexedPeripheralWord D
          (fun i ↦ i.castSucc) (fun i ↦ a l i.castSucc)
          (fun i ↦ ha l i.castSucc)
      · exact ha l (Fin.last k)
    have hstart : (wordDist D.alphabet.carrier 1 t : ℝ) ≤ eps := by
      dsimp [eps]
      norm_num
    have hend :
        (wordDist D.alphabet.carrier
          (vertex 1 wl wl.length) (vertex t wj wj.length) : ℝ) ≤ eps := by
      simp only [wl, wj, vertex_length_cyclicPeripheralPowerWord, one_mul]
      rw [hcommuteR]
      have hd := wordDist_left_invariant D.alphabet.carrier
        (orderedFinProduct (a l) ^ M)⁻¹
        (orderedFinProduct (a l) ^ M)
        (orderedFinProduct (a l) ^ M * t)
      have hsimp : (orderedFinProduct (a l) ^ M)⁻¹ *
          (orderedFinProduct (a l) ^ M * t) = t := by group
      rw [inv_mul_cancel, hsimp] at hd
      calc
        (wordDist D.alphabet.carrier (orderedFinProduct (a l) ^ M)
            (orderedFinProduct (a l) ^ M * t) : ℝ) =
            (wordDist D.alphabet.carrier 1 t : ℝ) := by
              exact_mod_cast hd.symm
        _ ≤ eps := hstart
    obtain ⟨ip, kp, iq, kq, lam, hcompL, hcompJ, hstepL, hstepJ, hmem⟩ :=
      hmatch 1 t wl wj hletterL hletterJ
        (isWOne_blockWord_finPeripheralWord (a l) M)
        (isWTwo_blockWord_finPeripheralWord D (a l) (hdeep l) M)
        (isWThree_blockWord_finPeripheralWord D (by omega) (a l) M)
        (isWOne_blockWord_finPeripheralWord (a j) N)
        (isWTwo_blockWord_finPeripheralWord D (a j) (hdeep j) N)
        (isWThree_blockWord_finPeripheralWord D (by omega) (a j) N)
        (by simpa [wl] using hlength) hstart hend
    obtain ⟨-, c, -, -, hcmem, hcrec, hterminalMem, -⟩ :=
      exists_fullCycleConnectorData_of_consecutiveMatches
        D (by omega) (a l) (a j) M N 1 t ip kp iq kq lam
          hcompL hcompJ hstepL hstepJ hmem
    have hprefix := matchedElementaryCommonPrefixConnectors_eq_one
      f (a l) (a j) c
      (fun i ↦ (hcommon l j i).symm)
      (hcentral l) hcmem hcrec hinter
    have hlastStart : c (Fin.last k).castSucc = 1 := hprefix (Fin.last k)
    have hlastRec := hcrec (Fin.last k)
    have hterminalEq :
        c (Fin.last (k + 1)) =
          (a l (Fin.last k))⁻¹ * a j (Fin.last k) := by
      simpa [hlastStart] using hlastRec
    apply hterminal l j hjl.symm
    rw [← hterminalEq]
    exact hterminalMem
  · let K : ℕ := 2
    let eps : ℝ := (wordDist D.alphabet.carrier 1 t : ℝ) + 1
    have heps : 0 < eps := by
      dsimp [eps]
      positivity
    have hK : 0 < K := by simp [K]
    obtain ⟨R, -, hmatch⟩ := hraw eps K heps hK
    let N := n * R
    let M := m * R
    let wj := cyclicPeripheralPowerWord (a j) N
    let wl := cyclicPeripheralPowerWord (a l) M
    have hcycle : 0 < k + 1 := by omega
    have hlength : R ≤ M * (k + 1) := by
      dsimp [M]
      exact (Nat.le_mul_of_pos_left R hm).trans
        (Nat.le_mul_of_pos_right (m * R) hcycle)
    have hoppR :
        t * orderedFinProduct (a j) ^ N * t⁻¹ =
          (orderedFinProduct (a l) ^ M)⁻¹ := by
      dsimp [N, M]
      calc
        t * orderedFinProduct (a j) ^ (n * R) * t⁻¹ =
            (t * orderedFinProduct (a j) ^ n * t⁻¹) ^ R := by
              rw [pow_mul, conj_pow]
        _ = ((orderedFinProduct (a l) ^ m)⁻¹) ^ R := by rw [hopp]
        _ = (orderedFinProduct (a l) ^ (m * R))⁻¹ := by
          rw [pow_mul, inv_pow]
    have hinverseR :
        t * (orderedFinProduct (a j) ^ N)⁻¹ =
          orderedFinProduct (a l) ^ M * t := by
      have hconjInv :
          t * (orderedFinProduct (a j) ^ N)⁻¹ * t⁻¹ =
            orderedFinProduct (a l) ^ M := by
        calc
          t * (orderedFinProduct (a j) ^ N)⁻¹ * t⁻¹ =
              (t * orderedFinProduct (a j) ^ N * t⁻¹)⁻¹ := by group
          _ = ((orderedFinProduct (a l) ^ M)⁻¹)⁻¹ := by rw [hoppR]
          _ = orderedFinProduct (a l) ^ M := inv_inv _
      calc
        t * (orderedFinProduct (a j) ^ N)⁻¹ =
            (t * (orderedFinProduct (a j) ^ N)⁻¹ * t⁻¹) * t := by group
        _ = orderedFinProduct (a l) ^ M * t := by rw [hconjInv]
    have hletterL : ∀ c ∈ wl, D.IsLetter c := by
      dsimp [wl]
      apply isLetter_of_mem_blockWord D (Fin.last k)
      · exact isLetter_indexedPeripheralWord D
          (fun i ↦ i.castSucc) (fun i ↦ a l i.castSucc)
          (fun i ↦ ha l i.castSucc)
      · exact ha l (Fin.last k)
    have hletterRevJ : ∀ c ∈ revWord wj, D.IsLetter c := by
      apply isLetter_of_mem_revWord D A.symmetricGenerating.inv_mem
      dsimp [wj]
      apply isLetter_of_mem_blockWord D (Fin.last k)
      · exact isLetter_indexedPeripheralWord D
          (fun i ↦ i.castSucc) (fun i ↦ a j i.castSucc)
          (fun i ↦ ha j i.castSucc)
      · exact ha j (Fin.last k)
    have hstart : (wordDist D.alphabet.carrier 1 t : ℝ) ≤ eps := by
      dsimp [eps]
      norm_num
    have hend :
        (wordDist D.alphabet.carrier
          (vertex 1 wl wl.length)
          (vertex t (revWord wj) (revWord wj).length) : ℝ) ≤ eps := by
      simp only [wl, wj, vertex_length, listVal_revWord,
        listVal_cyclicPeripheralPowerWord, one_mul]
      rw [hinverseR]
      have hd := wordDist_left_invariant D.alphabet.carrier
        (orderedFinProduct (a l) ^ M)⁻¹
        (orderedFinProduct (a l) ^ M)
        (orderedFinProduct (a l) ^ M * t)
      have hsimp : (orderedFinProduct (a l) ^ M)⁻¹ *
          (orderedFinProduct (a l) ^ M * t) = t := by group
      rw [inv_mul_cancel, hsimp] at hd
      calc
        (wordDist D.alphabet.carrier (orderedFinProduct (a l) ^ M)
            (orderedFinProduct (a l) ^ M * t) : ℝ) =
            (wordDist D.alphabet.carrier 1 t : ℝ) := by
              exact_mod_cast hd.symm
        _ ≤ eps := hstart
    obtain ⟨ip, kp, iq, kq, lam, hcompL, hcompRevJ, hstepL, hstepRevJ, -⟩ :=
      hmatch 1 t wl (revWord wj) hletterL hletterRevJ
        (isWOne_blockWord_finPeripheralWord (a l) M)
        (isWTwo_blockWord_finPeripheralWord D (a l) (hdeep l) M)
        (isWThree_blockWord_finPeripheralWord D (by omega) (a l) M)
        (isWOne_revWord (isWOne_blockWord_finPeripheralWord (a j) N))
        (isWTwo_revWord D A.symmetricGenerating.inv_mem
          (isWTwo_blockWord_finPeripheralWord D (a j) (hdeep j) N))
        (isWThree_revWord D
          (isWThree_blockWord_finPeripheralWord D (by omega) (a j) N))
        (by simpa [wl] using hlength) hstart hend
    have hsucc := cyclicSucc_componentIndex_of_consecutiveMatches
      D (by omega) (a l) M K ip kp lam hcompL hstepL 0 (by simp [K])
    have hpred := cyclicPred_componentIndex_of_consecutiveMatches_rev
      D (by omega) (a j) N K iq kq lam hcompRevJ hstepRevJ 0 (by simp [K])
    exact cyclicSucc_ne_cyclicPred (by omega) (lam 0) (hsucc.symm.trans hpred)

end HullSC
end GroupApproximation
