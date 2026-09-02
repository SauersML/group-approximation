import GroupApproximation.GGT.HullSCLemma49LongArc
import GroupApproximation.GGT.DGOPolygonGeodesicChain
import GroupApproximation.Sofic.HullSuitabilityGeometry

/-!
# Long cyclic geodesics give quasi-geodesic power boundaries

This module proves the local-to-global part of Osin's Lemma 6.2 in the exact
form used by Hull's Lemma 4.9.  If a shortest cyclic word has length at least
`8 * delta + 2`, divide every interval of its power path into blocks of length
`4 * delta + 1`.  One block and every pair of adjacent blocks have length at
most one period, hence are geodesic by
`wordDist_powerVertices_eq_of_sub_le_period`.  The block chain therefore has
zero local backtracking.  Hyperbolicity makes it progress linearly.

The result is a `(4, 8 * delta + 2)` quasi-geodesic estimate, uniform in the
word, exponent, group, and interval.  No loxodromic/elliptic dichotomy is used.
-/

namespace GroupApproximation

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric

universe u v

namespace HullGeometry

/-! ## A bounded finite version of the local-backtracking engine -/

/-- Local bounded backtracking gives progress on a finite chain.  This is the
bounded-index form of `chain_backtracking_and_progress`; it avoids extending a
finite power-boundary interval beyond its last vertex. -/
theorem finite_chain_backtracking_and_progress
    {X : Type v} [PseudoMetricSpace X]
    {delta C L : ℝ} (hdelta : IsHyperbolicSpace delta X)
    (hCdelta : 0 ≤ C + delta) (hgap : 2 * (C + delta) < L)
    {M : ℕ} (y : ℕ → X)
    (hedge : ∀ n : ℕ, n < M → L ≤ dist (y n) (y (n + 1)))
    (hlocal : ∀ n : ℕ, n + 2 ≤ M →
      gromovProduct (y n) (y (n + 2)) (y (n + 1)) ≤ C) :
    ∀ n ≤ M,
      (L - 2 * (C + delta)) * n ≤ dist (y 0) (y n) ∧
        (n < M →
          gromovProduct (y 0) (y (n + 1)) (y n) ≤ C + delta) := by
  intro n hn
  induction n with
  | zero =>
      constructor
      · simp
      · intro _
        have hzero : gromovProduct (y 0) (y 1) (y 0) = 0 := by
          unfold gromovProduct
          rw [dist_self, dist_comm (y 1) (y 0)]
          ring
        rw [hzero]
        exact hCdelta
  | succ n ih =>
      have hnM : n < M := by omega
      have hprev := ih (by omega)
      have hedgeN := hedge n hnM
      have hprogress :
          dist (y 0) (y n) + L - 2 * (C + delta) ≤
            dist (y 0) (y (n + 1)) := by
        have hback := hprev.2 hnM
        unfold gromovProduct at hback
        rw [dist_comm (y (n + 1)) (y n)] at hback
        linarith
      constructor
      · have hold := hprev.1
        push_cast
        linarith
      · intro hsuccM
        have hswap :=
          gromovProduct_add_swap_base (y 0) (y n) (y (n + 1))
        have hbehind : C + delta <
            gromovProduct (y 0) (y n) (y (n + 1)) := by
          linarith [hprev.2 hnM, hedgeN]
        have hloc := hlocal n (by omega)
        have hfar :
            gromovProduct (y n) (y (n + 2)) (y (n + 1)) + delta <
              gromovProduct (y 0) (y n) (y (n + 1)) := by
          linarith
        have hnext := gromovProduct_le_add_delta_of_lt hdelta hfar
        have hbound :
            gromovProduct (y 0) (y (n + 2)) (y (n + 1)) ≤
              C + delta := by
          linarith
        simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using hbound

end HullGeometry

namespace HullSC

open GroupApproximation.Manuscript.NonMF.TorsionFree

/-! ## Applying the finite engine to a power word -/

/-- A sufficiently long cyclic geodesic period makes every finite power word
a uniform `(4, 8 * delta + 2)` quasi-geodesic chain. -/
theorem isQuasiGeodesicChainAt_power_of_long_period
    {G : Type u} [Group G] {Lambda : Type*}
    (D : GGT.RelGenSet G Lambda) (N : Subgroup G) [N.Normal]
    {g : G} (hshort : IsShortestModuloConjugacy D.alphabet.carrier N g)
    {word : List (GGT.RelLetter G Lambda)}
    (hword : GGT.OsinComponents.IsGeodesicWord D 1 g word)
    {n delta : ℕ} (hn : 0 < n)
    (hdelta : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta)
    (hlong : 8 * delta + 2 ≤ word.length) :
    GGT.IsQuasiGeodesicChainAt D.alphabet.carrier 4 (8 * delta + 2)
      (fun i => GGT.OsinComponents.vertex 1
        (lemma49BoundaryPower word n) i)
      (lemma49BoundaryPower word n).length := by
  let power := lemma49BoundaryPower word n
  let blockLength := 4 * delta + 1
  let error := 8 * delta + 2
  have hwordNe : word ≠ [] := by
    intro hnil
    rw [hnil, List.length_nil] at hlong
    omega
  have hpowerLetters : ∀ a ∈ power, D.IsLetter a := by
    dsimp [power]
    exact isAdmissible_lemma49BoundaryPower hword.1 n
  have hblockPos : 0 < blockLength := by
    dsimp [blockLength]
    omega
  have htwoBlocks : 2 * blockLength ≤ word.length := by
    dsimp [blockLength]
    omega
  have hhyperbolic : IsHyperbolicSpace (delta : ℝ) (Cayley D.alphabet) :=
    GGT.isHyperbolicSpace_cayley_of_fourPoint D.alphabet hdelta
  intro i j hij hj
  have hupper : wordDist D.alphabet.carrier
      (GGT.OsinComponents.vertex 1 power i)
      (GGT.OsinComponents.vertex 1 power j) ≤ j - i :=
    GGT.OsinComponents.wordDist_vertex_le D hpowerLetters hij hj
  refine ⟨?_, hupper⟩
  let gap := j - i
  let chunks := gap / blockLength
  let remainder := gap % blockLength
  let chunkEnd := i + chunks * blockLength
  have hdivision : chunks * blockLength + remainder = gap := by
    simpa [chunks, remainder] using Nat.div_add_mod' gap blockLength
  have hremainder : remainder < blockLength := by
    dsimp [remainder]
    exact Nat.mod_lt _ hblockPos
  have hchunkEnd : chunkEnd ≤ j := by
    dsimp [chunkEnd, gap] at hdivision ⊢
    omega
  let y : ℕ → Cayley D.alphabet := fun t =>
    Cayley.of D.alphabet
      (GGT.OsinComponents.vertex 1 power (i + t * blockLength))
  have hedge : ∀ t : ℕ, t < chunks →
      (blockLength : ℝ) ≤ dist (y t) (y (t + 1)) := by
    intro t ht
    have hleft : i + t * blockLength ≤
        i + (t + 1) * blockLength := by
      exact Nat.add_le_add_left
        (Nat.mul_le_mul_right blockLength (by omega)) i
    have hright : i + (t + 1) * blockLength ≤ power.length := by
      have : i + (t + 1) * blockLength ≤ chunkEnd := by
        dsimp [chunkEnd]
        exact Nat.add_le_add_left
          (Nat.mul_le_mul_right blockLength (by omega)) i
      exact le_trans this (le_trans hchunkEnd hj)
    have hdist := wordDist_powerVertices_eq_of_sub_le_period D N hshort
      hword hn hwordNe hleft hright (by
        have : i + (t + 1) * blockLength - (i + t * blockLength) =
            blockLength := by
          rw [Nat.add_sub_add_left, Nat.add_mul, one_mul,
            Nat.add_sub_cancel_left]
        rw [this]
        exact le_trans (by omega : blockLength ≤ 2 * blockLength) htwoBlocks)
    have hstep : i + (t + 1) * blockLength -
        (i + t * blockLength) = blockLength := by
      rw [Nat.add_sub_add_left, Nat.add_mul, one_mul,
        Nat.add_sub_cancel_left]
    simp only [y, Cayley.dist_eq, Cayley.val_of]
    rw [hdist, hstep]
  have hlocal : ∀ t : ℕ, t + 2 ≤ chunks →
      gromovProduct (y t) (y (t + 2)) (y (t + 1)) ≤ 0 := by
    intro t ht
    have hindex (a b : ℕ) (hab : a ≤ b) (hb : b ≤ 2) :
        wordDist D.alphabet.carrier
            (GGT.OsinComponents.vertex 1 power (i + (t + a) * blockLength))
            (GGT.OsinComponents.vertex 1 power (i + (t + b) * blockLength)) =
          (b - a) * blockLength := by
      have hleft : i + (t + a) * blockLength ≤
          i + (t + b) * blockLength := by
        exact Nat.add_le_add_left
          (Nat.mul_le_mul_right blockLength (by omega)) i
      have hright : i + (t + b) * blockLength ≤ power.length := by
        have : i + (t + b) * blockLength ≤ chunkEnd := by
          dsimp [chunkEnd]
          exact Nat.add_le_add_left
            (Nat.mul_le_mul_right blockLength (by omega)) i
        exact le_trans this (le_trans hchunkEnd hj)
      have hsub : i + (t + b) * blockLength -
          (i + (t + a) * blockLength) = (b - a) * blockLength := by
        rw [Nat.add_sub_add_left, Nat.add_mul, Nat.add_mul,
          Nat.add_sub_add_left, Nat.sub_mul]
      have hperiodBound : i + (t + b) * blockLength -
          (i + (t + a) * blockLength) ≤ word.length := by
        rw [hsub]
        exact le_trans
          (Nat.mul_le_mul_right blockLength (by omega : b - a ≤ 2))
          htwoBlocks
      have hdist := wordDist_powerVertices_eq_of_sub_le_period D N hshort
        hword hn hwordNe hleft hright hperiodBound
      rw [hsub] at hdist
      exact hdist
    have h01 := hindex 0 1 (by omega) (by omega)
    have h12 := hindex 1 2 (by omega) (by omega)
    have h02 := hindex 0 2 (by omega) (by omega)
    norm_num at h01 h12 h02
    have h21 : wordDist D.alphabet.carrier
        (GGT.OsinComponents.vertex 1 power (i + (t + 2) * blockLength))
        (GGT.OsinComponents.vertex 1 power (i + (t + 1) * blockLength)) =
        blockLength := by
      calc
        _ = wordDist D.alphabet.carrier
            (GGT.OsinComponents.vertex 1 power
              (i + (t + 1) * blockLength))
            (GGT.OsinComponents.vertex 1 power
              (i + (t + 2) * blockLength)) :=
          wordDist_comm D.alphabet.symmetricGenerating _ _
        _ = blockLength := h12
    simp only [gromovProduct, y, Cayley.dist_eq, Cayley.val_of]
    rw [h01, h21, h02]
    push_cast
    linarith
  have hprogressReal :=
    (finite_chain_backtracking_and_progress hhyperbolic
      (C := 0) (L := (blockLength : ℝ)) (by positivity) (by
        dsimp [blockLength]
        push_cast
        linarith) y hedge hlocal chunks le_rfl).1
  have hprogress : (2 * delta + 1) * chunks ≤
      wordDist D.alphabet.carrier
        (GGT.OsinComponents.vertex 1 power i)
        (GGT.OsinComponents.vertex 1 power chunkEnd) := by
    have hcast : (((2 * delta + 1) * chunks : ℕ) : ℝ) ≤
        ((wordDist D.alphabet.carrier (y 0).val (y chunks).val : ℕ) : ℝ) := by
      dsimp [blockLength] at hprogressReal
      push_cast at hprogressReal
      convert hprogressReal using 1 <;> ring
    have hnat : (2 * delta + 1) * chunks ≤
        wordDist D.alphabet.carrier (y 0).val (y chunks).val := by
      exact_mod_cast hcast
    simpa only [y, Nat.zero_mul, Nat.add_zero, chunkEnd,
      Cayley.val_of] using hnat
  have htail : wordDist D.alphabet.carrier
      (GGT.OsinComponents.vertex 1 power chunkEnd)
      (GGT.OsinComponents.vertex 1 power j) ≤ remainder := by
    have hraw := GGT.OsinComponents.wordDist_vertex_le D hpowerLetters
      hchunkEnd hj
    have hjsub : j - chunkEnd = remainder := by
      dsimp [chunkEnd, gap] at hdivision ⊢
      omega
    rwa [hjsub] at hraw
  have hlowerNat : (2 * delta + 1) * chunks ≤
      wordDist D.alphabet.carrier
          (GGT.OsinComponents.vertex 1 power i)
          (GGT.OsinComponents.vertex 1 power j) + remainder := by
    have htail' : wordDist D.alphabet.carrier
        (GGT.OsinComponents.vertex 1 power j)
        (GGT.OsinComponents.vertex 1 power chunkEnd) ≤ remainder := by
      rw [wordDist_comm D.alphabet.symmetricGenerating]
      exact htail
    have htri := wordDist_triangle D.alphabet.symmetricGenerating
      (GGT.OsinComponents.vertex 1 power i)
      (GGT.OsinComponents.vertex 1 power j)
      (GGT.OsinComponents.vertex 1 power chunkEnd)
    omega
  have hfour : gap ≤ 4 *
      (wordDist D.alphabet.carrier
          (GGT.OsinComponents.vertex 1 power i)
          (GGT.OsinComponents.vertex 1 power j) + error) := by
    dsimp [blockLength, error] at hdivision hremainder ⊢
    omega
  have hfourReal : (gap : ℝ) ≤ 4 *
      ((wordDist D.alphabet.carrier
          (GGT.OsinComponents.vertex 1 power i)
          (GGT.OsinComponents.vertex 1 power j) : ℕ) : ℝ) +
        (error : ℝ)) := by
    exact_mod_cast hfour
  dsimp [gap, error] at hfourReal ⊢
  norm_num
  linarith

/-! ## Model check -/

/-- On the one-point group the long-period premise is impossible because a
geodesic identity word is empty. -/
theorem no_long_geodesic_period_trivialModel
    {Lambda : Type*} (D : GGT.RelGenSet PUnit Lambda)
    {word : List (GGT.RelLetter PUnit Lambda)}
    (hword : GGT.OsinComponents.IsGeodesicWord D 1 1 word)
    (delta : ℕ) : ¬ 8 * delta + 2 ≤ word.length := by
  intro hlong
  have hempty : word = [] := by
    apply List.eq_nil_of_length_eq_zero
    have hlen := hword.2.2
    simpa [wordDist_one_left] using hlen
  rw [hempty, List.length_nil] at hlong
  omega

end HullSC
end GroupApproximation
