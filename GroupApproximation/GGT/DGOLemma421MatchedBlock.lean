import GroupApproximation.GGT.DGOLemma421MatchedInterval

/-!
# From consecutive rank matches to the literal DGO block

The rank interval theorem constructs the natural-indexed component block in
Lemma 4.21(b). Its separator fields follow from (W1), and maximality follows
from (W3); neither is supplied as a new geometric premise.
-/

namespace GroupApproximation.GGT.OsinComponents

universe u w
variable {G : Type u} [Group G] {Lambda : Type w}

/-- Consecutive matching ranks give the existing ordered-block payload,
including both separator and maximal-component conditions. -/
theorem orderedBlockPayload_of_rank_matches
    {D : RelGenSet G Lambda} {P Q : List (RelLetter G Lambda)} {vp vq : G} {K : ℕ}
    (hW1P : WWord.IsWOne P) (hW1Q : WWord.IsWOne Q)
    (hW3P : WWord.IsWThree D P) (hW3Q : WWord.IsWThree D Q)
    (s : Fin (peripheralPositions P).card) (a : Fin (peripheralPositions Q).card)
    (hrun : ∀ k : ℕ, k < K →
      ∃ r : Fin (peripheralPositions P).card, ∃ c : Fin (peripheralPositions Q).card,
        r.val = s.val + k ∧ c.val = a.val + k ∧
        (peripheralOccurrence Q c).label = (peripheralOccurrence P r).label ∧
        (vertex vp P (peripheralOccurrence P r).pos)⁻¹ *
          vertex vq Q (peripheralOccurrence Q c).pos ∈ D.fam (peripheralOccurrence P r).label) :
    Nonempty (DGO421OrderedBlockPayload D vp vq P Q K) := by
  classical
  let rp : ℕ → Fin (peripheralPositions P).card := fun k =>
    if hk : k < K then Classical.choose (hrun k hk) else s
  let rq : ℕ → Fin (peripheralPositions Q).card := fun k =>
    if hk : k < K then Classical.choose (Classical.choose_spec (hrun k hk)) else a
  have hspec : ∀ k : ℕ, k < K →
      (rp k).val = s.val + k ∧ (rq k).val = a.val + k ∧
        (peripheralOccurrence Q (rq k)).label = (peripheralOccurrence P (rp k)).label ∧
        (vertex vp P (peripheralOccurrence P (rp k)).pos)⁻¹ *
          vertex vq Q (peripheralOccurrence Q (rq k)).pos ∈
            D.fam (peripheralOccurrence P (rp k)).label := by
    intro k hk
    dsimp [rp, rq]
    rw [dif_pos hk, dif_pos hk]
    exact Classical.choose_spec (Classical.choose_spec (hrun k hk))
  refine ⟨{
    ip := fun k => (peripheralOccurrence P (rp k)).pos
    kp := fun k => (peripheralOccurrence P (rp k)).pos + 1
    iq := fun k => (peripheralOccurrence Q (rq k)).pos
    kq := fun k => (peripheralOccurrence Q (rq k)).pos + 1
    lam := fun k => (peripheralOccurrence P (rp k)).label
    pcomp := fun k _ => PeripheralOccurrence.isComp hW3P (rp k)
    qcomp := ?_
    psep := ?_
    qsep := ?_
    cosetMatch := fun k hk => (hspec k hk).2.2.2 }⟩
  · intro k hk
    simpa only [(hspec k hk).2.2.1] using PeripheralOccurrence.isComp hW3Q (rq k)
  · intro k hk
    have hr := (hspec k (by omega)).1
    have hrnext := (hspec (k + 1) hk).1
    have hbound : (rp k).val + 1 < (peripheralPositions P).card := by
      have := (rp (k + 1)).isLt
      omega
    have heq : (⟨(rp k).val + 1, hbound⟩ : Fin (peripheralPositions P).card) = rp (k + 1) := by
      apply Fin.ext
      change (rp k).val + 1 = (rp (k + 1)).val
      omega
    simpa only [heq] using PeripheralOccurrence.baseEdgeOrTrivial_succ hW1P (rp k) hbound
  · intro k hk
    have hr := (hspec k (by omega)).2.1
    have hrnext := (hspec (k + 1) hk).2.1
    have hbound : (rq k).val + 1 < (peripheralPositions Q).card := by
      have := (rq (k + 1)).isLt
      omega
    have heq : (⟨(rq k).val + 1, hbound⟩ : Fin (peripheralPositions Q).card) = rq (k + 1) := by
      apply Fin.ext
      change (rq k).val + 1 = (rq (k + 1)).val
      omega
    simpa only [heq] using PeripheralOccurrence.baseEdgeOrTrivial_succ hW1Q (rq k) hbound


open GroupApproximation.WordMetric

/-- A forward pair with a sufficiently large rank gap yields the actual
length-`K` ordered component block of DGO 4.21(b). The remaining global task
is to produce such a forward pair from oriented endpoint closeness. -/
theorem orderedBlockPayload_of_forward_matches_of_uniformBounds
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
      vertex vq Q (peripheralOccurrence Q b).pos ∈ D.fam (peripheralOccurrence P t).label)
    {K : ℕ} (hK : K ≤ t.val - s.val + 1) :
    Nonempty (DGO421OrderedBlockPayload D vp vq P Q K) := by
  obtain ⟨_, hrun⟩ := rank_matches_on_interval_of_uniformBounds hC11 hbound hproj hbase
    hletP hletQ hW1P hW1Q hW2P hW2Q hW3P hW3Q hqgP hqgQ hst hab
    hlabelA hlabelB hmatchA hmatchB
  apply orderedBlockPayload_of_rank_matches hW1P hW1Q hW3P hW3Q s a
  intro k hk
  exact hrun k (by omega)

end GroupApproximation.GGT.OsinComponents

#audit_axioms GroupApproximation.GGT.OsinComponents.orderedBlockPayload_of_rank_matches

#audit_axioms GroupApproximation.GGT.OsinComponents.orderedBlockPayload_of_forward_matches_of_uniformBounds
