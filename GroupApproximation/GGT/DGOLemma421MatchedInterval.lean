import GroupApproximation.GGT.DGOLemma421RankInterpolation
import GroupApproximation.GGT.DGOLemma421OrderedBridge

/-!
# Consecutive component matches between forward matched endpoints

A forward pair of matched components determines a full consecutive run.
The matching relation is a partial bijection by isolation of the two W-words;
the minimal-gap theorem fills the interval one successor at a time.
-/

namespace GroupApproximation.GGT.OsinComponents

open GroupApproximation.WordMetric

universe u w
variable {G : Type u} [Group G] {Lambda : Type w}

/-- Two components of a deep W-word that meet the same peripheral coset are
the same canonical occurrence. -/
theorem peripheralOccurrence_eq_of_common_coset
    {D : RelGenSet G Lambda} {C : ℕ} (hC : 0 < C)
    (hbound : DGOUniformSumBound D 1 1 C)
    {P : List (RelLetter G Lambda)} (hletP : ∀ letter ∈ P, D.IsLetter letter)
    (hW1P : WWord.IsWOne P) (hW2P : WWord.IsWTwo D (50 * C) P)
    (hW3P : WWord.IsWThree D P) (v z : G)
    {s t : Fin (peripheralPositions P).card}
    (hlabel : (peripheralOccurrence P t).label = (peripheralOccurrence P s).label)
    (hs : (vertex v P (peripheralOccurrence P s).pos)⁻¹ * z ∈
      D.fam (peripheralOccurrence P s).label)
    (ht : (vertex v P (peripheralOccurrence P t).pos)⁻¹ * z ∈
      D.fam (peripheralOccurrence P t).label) : s = t := by
  by_contra hne
  apply peripheralOccurrence_not_connected_of_uniformBound hC hbound hletP
    hW1P hW2P hW3P v hne hlabel
  rw [hlabel] at ht
  have hm := (D.fam (peripheralOccurrence P s).label).mul_mem hs
    ((D.fam (peripheralOccurrence P s).label).inv_mem ht)
  change (vertex v P (peripheralOccurrence P s).pos)⁻¹ *
    vertex v P (peripheralOccurrence P t).pos ∈ _
  convert hm using 1
  group

/-- Between any two forward matches, all component ranks match in consecutive
order, and the source and target rank gaps agree. -/
theorem rank_matches_on_interval_of_uniformBounds
    {D : RelGenSet G Lambda} {C11 C414 : ℕ} (hC11 : 0 < C11)
    (hbound : DGOUniformSumBound D 1 1 C11)
    (hproj : ∀ (n : ℕ) (v : G) (word : List (RelLetter G Lambda)),
      IsQuasiGeodesicPolygon D 4 1 n v word →
      ∀ (nu : Lambda) (i k : ℕ), IsComp nu word i k → IsIsolated D.fam nu v word i →
        (vertex v word i)⁻¹ * vertex v word k ∈ D.relBall nu (C414 * n))
    (hbase : DGO421BaseSymmetric D)
    {P Q : List (RelLetter G Lambda)} {vp vq : G}
    (hletP : ∀ letter ∈ P, D.IsLetter letter) (hletQ : ∀ letter ∈ Q, D.IsLetter letter)
    (hW1P : WWord.IsWOne P) (hW1Q : WWord.IsWOne Q)
    (hW2P : WWord.IsWTwo D (max (50 * C11) (C414 * 4)) P)
    (hW2Q : WWord.IsWTwo D (max (50 * C11) (C414 * 4)) Q)
    (hW3P : WWord.IsWThree D P) (hW3Q : WWord.IsWThree D Q)
    (hqgP : ∀ i j : ℕ, i ≤ j → j ≤ P.length →
      ((j - i : ℕ) : ℝ) / 4 - 1 ≤
        (wordDist D.alphabet.carrier (vertex vp P i) (vertex vp P j) : ℝ))
    (hqgQ : ∀ i j : ℕ, i ≤ j → j ≤ Q.length →
      ((j - i : ℕ) : ℝ) / 4 - 1 ≤
        (wordDist D.alphabet.carrier (vertex vq Q i) (vertex vq Q j) : ℝ))
    {s t : Fin (peripheralPositions P).card}
    {a b : Fin (peripheralPositions Q).card}
    (hst : s < t) (hab : a < b)
    (hlabelA : (peripheralOccurrence Q a).label = (peripheralOccurrence P s).label)
    (hlabelB : (peripheralOccurrence Q b).label = (peripheralOccurrence P t).label)
    (hmatchA : (vertex vp P (peripheralOccurrence P s).pos)⁻¹ *
      vertex vq Q (peripheralOccurrence Q a).pos ∈ D.fam (peripheralOccurrence P s).label)
    (hmatchB : (vertex vp P (peripheralOccurrence P t).pos)⁻¹ *
      vertex vq Q (peripheralOccurrence Q b).pos ∈ D.fam (peripheralOccurrence P t).label) :
    t.val - s.val = b.val - a.val ∧
      ∀ k : ℕ, k ≤ t.val - s.val →
      ∃ r : Fin (peripheralPositions P).card, ∃ c : Fin (peripheralPositions Q).card,
        r.val = s.val + k ∧ c.val = a.val + k ∧
        (peripheralOccurrence Q c).label = (peripheralOccurrence P r).label ∧
        (vertex vp P (peripheralOccurrence P r).pos)⁻¹ *
          vertex vq Q (peripheralOccurrence Q c).pos ∈ D.fam (peripheralOccurrence P r).label := by
  let M : Fin (peripheralPositions P).card → Fin (peripheralPositions Q).card → Prop :=
    fun r c => (peripheralOccurrence Q c).label = (peripheralOccurrence P r).label ∧
      (vertex vp P (peripheralOccurrence P r).pos)⁻¹ *
        vertex vq Q (peripheralOccurrence Q c).pos ∈ D.fam (peripheralOccurrence P r).label
  have hW2isoP : WWord.IsWTwo D (50 * C11) P := by
    intro i nu g hread hmem
    exact hW2P i nu g hread (relBall_mono_radius D nu (Nat.le_max_left _ _) hmem)
  have hW2isoQ : WWord.IsWTwo D (50 * C11) Q := by
    intro i nu g hread hmem
    exact hW2Q i nu g hread (relBall_mono_radius D nu (Nat.le_max_left _ _) hmem)
  apply rank_matches_on_interval_of_successors M ?_ ?_ ?_ hst hab
    ⟨hlabelA, hmatchA⟩ ⟨hlabelB, hmatchB⟩
  · intro r t c hrc htc
    exact peripheralOccurrence_eq_of_common_coset hC11 hbound hletP hW1P hW2isoP hW3P
      vp (vertex vq Q (peripheralOccurrence Q c).pos) (htc.1.symm.trans hrc.1) hrc.2 htc.2
  · intro r c d hrc hrd
    apply peripheralOccurrence_eq_of_common_coset hC11 hbound hletQ hW1Q hW2isoQ hW3Q
      vq (vertex vp P (peripheralOccurrence P r).pos) (hrd.1.trans hrc.1.symm)
    · rw [hrc.1]
      simpa only [mul_inv_rev, inv_inv] using
        (D.fam (peripheralOccurrence P r).label).inv_mem hrc.2
    · rw [hrd.1]
      simpa only [mul_inv_rev, inv_inv] using
        (D.fam (peripheralOccurrence P r).label).inv_mem hrd.2
  · intro s t a b hst hab hsa htb
    exact exists_successor_rank_match_of_uniformBounds hC11 hbound hproj hbase
      hletP hletQ hW1P hW1Q hW2P hW2Q hW3P hW3Q hqgP hqgQ hst hab
      hsa.1 htb.1 hsa.2 htb.2

end GroupApproximation.GGT.OsinComponents

#audit_axioms GroupApproximation.GGT.OsinComponents.peripheralOccurrence_eq_of_common_coset
#audit_axioms GroupApproximation.GGT.OsinComponents.rank_matches_on_interval_of_uniformBounds
