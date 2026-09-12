import GroupApproximation.GGT.DGOProposition414ArcQuasi

/-!
# General quasi-geodesic estimates on both inherited balanced arcs

The component-surgery record may use any finite bookkeeping error. These
lemmas transport an independently supplied genuine `(mu,c)` estimate to the
same first and wrapped second arcs, with no change to either parameter.
Endpoint fragments of omitted single-edge targets are trivial.
-/

namespace GroupApproximation.GGT.DGOProposition414.BalancedSplitData

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents
open GroupApproximation.WordMetric

universe u w
variable {G : Type u} [Group G] {Λ : Type w}

/-- The first inherited arc preserves the original general parameters. -/
theorem firstArc_quasi_at
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (mu c : ℝ) (hc : 0 ≤ c)
    (hquasi : ∀ s : ℕ, s < n → s ∉ P.target → ∀ p q : ℕ,
      P.cut s ≤ p → p ≤ q → q ≤ P.cut (s + 1) →
      ((q - p : ℕ) : ℝ) / mu - c ≤
        ((wordDist D.alphabet.carrier
          (vertex P.basepoint P.word p) (vertex P.basepoint P.word q) : ℕ) : ℝ)) :
    ∀ s : ℕ, s < B.secondSide - B.firstSide + 1 →
      s ∉ B.firstArcTargetSides → ∀ p q : ℕ,
      B.firstArcCut s ≤ p → p ≤ q → q ≤ B.firstArcCut (s + 1) →
      ((q - p : ℕ) : ℝ) / mu - c ≤
        ((wordDist D.alphabet.carrier
          (vertex B.firstBase B.firstArc p)
          (vertex B.firstBase B.firstArc q) : ℕ) : ℝ) := by
  have horder := B.side_order
  have hsecond := B.secondSide_lt
  intro s hs hsTarget p q hp hpq hq
  rcases B.firstArc_offTarget_source_or_trivial hs hsTarget with
      hparent | htrivial
  · have hsourceLt : B.firstSide + s < n := by omega
    have hleft : P.cut (B.firstSide + s) ≤ B.firstVertex + p := by
      by_cases hs0 : s = 0
      · subst s
        simpa only [Nat.add_zero] using
          B.firstVertex_mem.1.trans (Nat.le_add_right B.firstVertex p)
      · have hcut := B.firstArcCut_of_pos (s := s) (by omega) (by omega)
        rw [hcut] at hp
        have hvertex := B.firstVertex_mem.2.trans
          (P.polygonCut.mono_le (show B.firstSide + 1 ≤
            B.firstSide + s by omega))
        omega
    have hright : B.firstVertex + q ≤ P.cut (B.firstSide + s + 1) := by
      have hvertices := B.split_vertices_ordered
      by_cases hlast : s = B.secondSide - B.firstSide
      · subst s
        rw [B.firstArcCut_last_succ] at hq
        rw [show B.firstSide + (B.secondSide - B.firstSide) + 1 =
          B.secondSide + 1 by omega]
        have hvertex := B.secondVertex_mem.2
        omega
      · have hslt : s < B.secondSide - B.firstSide := by omega
        have hcut := B.firstArcCut_succ_of_lt (s := s) hslt
        rw [hcut] at hq
        have hvertex := B.firstVertex_mem.2.trans
          (P.polygonCut.mono_le (show B.firstSide + 1 ≤
            B.firstSide + s + 1 by omega))
        omega
    have hparentQuasi := hquasi (B.firstSide + s) hsourceLt hparent
      (B.firstVertex + p) (B.firstVertex + q) hleft
      (Nat.add_le_add_left hpq _) hright
    have hbase : B.refinedCut (B.firstSide + 1) = B.firstVertex := by
      simp [refinedCut, splitPairCut_left B.side_order]
    have hqArc : q ≤ B.refinedCut (B.secondSide + 2) -
        B.refinedCut (B.firstSide + 1) := by
      have hsideLe : s + 1 ≤ B.secondSide - B.firstSide + 1 := by omega
      have hcutLe := B.firstArc_isCutPath.cut.mono_le hsideLe
      have hqEnd := hq.trans hcutLe
      simpa only [firstArcCut,
        show B.firstSide + 1 + (B.secondSide - B.firstSide + 1) =
          B.secondSide + 2 by omega] using hqEnd
    have hpArc : p ≤ B.refinedCut (B.secondSide + 2) -
        B.refinedCut (B.firstSide + 1) := hpq.trans hqArc
    have hvp : vertex B.firstBase B.firstArc p =
        vertex P.basepoint P.word (B.firstVertex + p) := by
      simpa only [firstBase, firstArc, hbase] using
        vertex_arcWord P.word P.basepoint B.refinedCut hpArc
    have hvq : vertex B.firstBase B.firstArc q =
        vertex P.basepoint P.word (B.firstVertex + q) := by
      simpa only [firstBase, firstArc, hbase] using
        vertex_arcWord P.word P.basepoint B.refinedCut hqArc
    have hdiff : B.firstVertex + q - (B.firstVertex + p) = q - p := by
      omega
    simpa only [hvp, hvq, hdiff] using
      hparentQuasi
  · have hpqEq : p = q := by omega
    subst q
    simpa only [Nat.sub_self, Nat.cast_zero, zero_div, wordDist_self, zero_sub] using
      (neg_nonpos.mpr hc)

/-- The wrapped second arc preserves the original general parameters. -/
theorem secondArc_quasi_at
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (mu c : ℝ) (hc : 0 ≤ c)
    (hquasi : ∀ s : ℕ, s < n → s ∉ P.target → ∀ p q : ℕ,
      P.cut s ≤ p → p ≤ q → q ≤ P.cut (s + 1) →
      ((q - p : ℕ) : ℝ) / mu - c ≤
        ((wordDist D.alphabet.carrier
          (vertex P.basepoint P.word p) (vertex P.basepoint P.word q) : ℕ) : ℝ)) :
    ∀ s : ℕ, s < (n - B.secondSide) + B.firstSide + 1 →
      s ∉ B.secondArcTargetSides → ∀ p q : ℕ,
      B.secondArcCut s ≤ p → p ≤ q → q ≤ B.secondArcCut (s + 1) →
      ((q - p : ℕ) : ℝ) / mu - c ≤
        ((wordDist D.alphabet.carrier
          (vertex B.secondBase B.secondArc p)
          (vertex B.secondBase B.secondArc q) : ℕ) : ℝ) := by
  have horder := B.side_order
  have hsecond := B.secondSide_lt
  intro s hs hsTarget p q hp hpq hq
  rcases B.secondArc_offTarget_source_or_trivial hs hsTarget with
      hparent | htrivial
  · have hsecondLe : B.secondVertex ≤ P.word.length :=
      B.secondVertex_mem.2.trans
        (P.polygonCut.le_length (Nat.succ_le_iff.mpr B.secondSide_lt))
    have hqArc : q ≤
        (P.word.length - B.secondVertex) + B.firstVertex := by
      have hsideLe : s + 1 ≤
          (n - B.secondSide) + B.firstSide + 1 := by omega
      have hcutLe := B.secondArc_isCutPath.cut.mono_le hsideLe
      have hqEnd := hq.trans hcutLe
      rwa [B.secondArcCut_finish] at hqEnd
    have hpArc : p ≤
        (P.word.length - B.secondVertex) + B.firstVertex := hpq.trans hqArc
    have hleftCorner : B.refinedCut (B.firstSide + 1) =
        B.firstVertex := by
      simp [refinedCut, splitPairCut_left B.side_order]
    have hrightCorner : B.refinedCut (B.secondSide + 2) =
        B.secondVertex := by
      simp [refinedCut, splitPairCut_right]
    have hcornerOrder : B.refinedCut (B.firstSide + 1) ≤
        B.refinedCut (B.secondSide + 2) := by
      rw [hleftCorner, hrightCorner]
      exact B.split_vertices_ordered
    have hvpRot := vertex_secondHalf_rotWord P.word P.basepoint B.refinedCut
      hcornerOrder (by rwa [hrightCorner])
      (by simpa only [hleftCorner, hrightCorner] using hpArc)
      ([] : List (RelLetter G Λ))
    have hvqRot := vertex_secondHalf_rotWord P.word P.basepoint B.refinedCut
      hcornerOrder (by rwa [hrightCorner])
      (by simpa only [hleftCorner, hrightCorner] using hqArc)
      ([] : List (RelLetter G Λ))
    have hvp : vertex B.secondBase B.secondArc p =
        vertex (vertex P.basepoint P.word B.secondVertex)
          (rotWord P.word B.secondVertex) p := by
      simpa only [secondBase, secondArc, secondHalf, List.append_nil,
        hleftCorner, hrightCorner] using hvpRot
    have hvq : vertex B.secondBase B.secondArc q =
        vertex (vertex P.basepoint P.word B.secondVertex)
          (rotWord P.word B.secondVertex) q := by
      simpa only [secondBase, secondArc, secondHalf, List.append_nil,
        hleftCorner, hrightCorner] using hvqRot
    by_cases htail : s < n - B.secondSide
    · have hsource : B.secondArcSource s = B.secondSide + s := by
        simp [secondArcSource, htail]
      have hsourceLt : B.secondArcSource s < n := by
        rw [hsource]
        omega
      have hleft : P.cut (B.secondArcSource s) ≤
          B.secondVertex + p := by
        by_cases hs0 : s = 0
        · subst s
          simp only [secondArcSource, if_pos (show 0 < n - B.secondSide by
            omega), Nat.add_zero]
          have hvertex := B.secondVertex_mem.1
          omega
        · have hcut := B.secondArcCut_of_pos_le_tail (s := s)
            (by omega) (by omega)
          rw [hcut] at hp
          have hvertex := B.secondVertex_mem.2.trans
            (P.polygonCut.mono_le (show B.secondSide + 1 ≤
              B.secondArcSource s by rw [hsource]; omega))
          rw [hsource] at hvertex ⊢
          omega
      have hright : B.secondVertex + q ≤
          P.cut (B.secondArcSource s + 1) := by
        have hcut := B.secondArcCut_of_pos_le_tail (s := s + 1)
          (by omega) (by omega)
        rw [hcut] at hq
        rw [show B.secondSide + (s + 1) =
          B.secondSide + s + 1 by omega] at hq
        rw [hsource]
        have hvertex := B.secondVertex_mem.2.trans
          (P.polygonCut.mono_le (show B.secondSide + 1 ≤
            B.secondSide + s + 1 by omega))
        omega
      have hqSuffix : q ≤ P.word.length - B.secondVertex := by
        have hcutLen := P.polygonCut.le_length
          (show B.secondArcSource s + 1 ≤ n by omega)
        omega
      have hpSuffix : p ≤ P.word.length - B.secondVertex :=
        hpq.trans hqSuffix
      have hvpOriginal := vertex_rotWord_le P.basepoint P.word hsecondLe p
        hpSuffix
      have hvqOriginal := vertex_rotWord_le P.basepoint P.word hsecondLe q
        hqSuffix
      have hparentQuasi := hquasi (B.secondArcSource s) hsourceLt hparent
        (B.secondVertex + p) (B.secondVertex + q) hleft
        (Nat.add_le_add_left hpq _) hright
      have hdiff : B.secondVertex + q - (B.secondVertex + p) = q - p := by
        omega
      simpa only [hvp, hvq, hvpOriginal, hvqOriginal, hdiff] using
        hparentQuasi
    · have hsource : B.secondArcSource s =
          s - (n - B.secondSide) := by
        simp [secondArcSource, htail]
      have hsourceLe : B.secondArcSource s ≤ B.firstSide := by
        rw [hsource]
        omega
      have hsourceLt : B.secondArcSource s < n := by omega
      have hsEq : s =
          (n - B.secondSide) + B.secondArcSource s := by
        rw [hsource]
        omega
      have hcutStart := B.secondArcCut_tail_add hsourceLe
      rw [← hsEq] at hcutStart
      rw [hcutStart] at hp
      let suffix := P.word.length - B.secondVertex
      have hpAfter : suffix ≤ p := by dsimp [suffix]; omega
      have hqAfter : suffix ≤ q := hpAfter.trans hpq
      have hleft : P.cut (B.secondArcSource s) ≤ p - suffix := by
        dsimp [suffix]
        omega
      have hright : q - suffix ≤ P.cut (B.secondArcSource s + 1) := by
        by_cases hlast : B.secondArcSource s = B.firstSide
        · have hsLast : s =
              (n - B.secondSide) + B.firstSide := by omega
          rw [hsLast, B.secondArcCut_finish] at hq
          rw [hlast]
          have hvertex := B.firstVertex_mem.2
          dsimp [suffix]
          omega
        · have hnextLe : B.secondArcSource s + 1 ≤ B.firstSide := by omega
          have hsNext : s + 1 =
              (n - B.secondSide) + (B.secondArcSource s + 1) := by omega
          have hcutFinish := B.secondArcCut_tail_add hnextLe
          rw [← hsNext] at hcutFinish
          rw [hcutFinish] at hq
          dsimp [suffix]
          omega
      have hpPrefix : p - suffix ≤ B.secondVertex := by
        have hfirstSecond := B.split_vertices_ordered
        dsimp [suffix]
        omega
      have hqPrefix : q - suffix ≤ B.secondVertex := by
        have hfirstSecond := B.split_vertices_ordered
        dsimp [suffix]
        omega
      have hvpOriginal := vertex_rotWord_add P.basepoint P.word hsecondLe
        P.closed p (p - suffix) (by dsimp [suffix]; omega) hpPrefix
      have hvqOriginal := vertex_rotWord_add P.basepoint P.word hsecondLe
        P.closed q (q - suffix) (by dsimp [suffix]; omega) hqPrefix
      have hparentQuasi := hquasi (B.secondArcSource s) hsourceLt hparent
        (p - suffix) (q - suffix) hleft (by omega) hright
      have hdiff : q - suffix - (p - suffix) = q - p := by omega
      simpa only [hvp, hvq, hvpOriginal, hvqOriginal, hdiff] using
        hparentQuasi
  · have hpqEq : p = q := by omega
    subst q
    simpa only [Nat.sub_self, Nat.cast_zero, zero_div, wordDist_self, zero_sub] using
      (neg_nonpos.mpr hc)

end GroupApproximation.GGT.DGOProposition414.BalancedSplitData

#audit_axioms GroupApproximation.GGT.DGOProposition414.BalancedSplitData.firstArc_quasi_at
#audit_axioms GroupApproximation.GGT.DGOProposition414.BalancedSplitData.secondArc_quasi_at
