import GroupApproximation.Sofic.GreendlingerDeepInvariant
import GroupApproximation.Sofic.GreendlingerNonConfinedProgress

/-! # Premise-free sharp gate through the sound drop invariant -/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-- The sound recursive descent over a composite deep landing and the repaired
shallow disjunction.  The measure is the same `n` as in
`greendlingerAtSharp_drop_of_lands`; only the shallow branch changes. -/
theorem greendlingerAtSharp_drop_of_lands'
    [DecidableEq α] {R : Set (List (α × Bool))} {lam : ℚ}
    (hcyc : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r)
    (hne : ∀ r ∈ R, r ≠ []) (hlam : lam ≤ 1 / 6)
    (hmetric : MetricSmallCancellation R lam)
    (hdeep : DeepCompositeLandsSharp R lam)
    (hland : LandingProductionSharp' R lam) :
    ∀ (n : ℕ) (e : List (FreeGroup α × List (α × Bool)))
      (c t w : List (α × Bool)) (N i : ℕ),
      e.length ≤ n → FreeGroup.IsReduced w → t ∈ symmetrization R →
      FreeGroup.IsReduced (palindrome c t) →
      IsMinimalConjExpr R ((FreeGroup.mk c, t) :: e) (FreeGroup.mk w) →
      (i : ℚ) < lam * (t.length : ℚ) → N ≤ c.length + i →
      GreendlingerAtSharp R lam 0 (w.drop N) := by
  intro n
  induction n with
  | zero =>
      intro e c t w N i hlen hw ht hredp hmin hi hN
      cases e with
      | cons _ e' =>
          simp only [List.length_cons] at hlen
          exact absurd hlen (by omega)
      | nil =>
          obtain ⟨P', M, B', heq, hgw, hwe⟩ :=
            exists_leading_cancellation hw hredp hmin.2.1
          have hnil : FreeGroup.invRev M ++ B' = [] := by
            rw [← hgw, conjEval_nil]
            exact FreeGroup.toWord_eq_nil_iff.mpr rfl
          have hz := congrArg List.length hnil
          rw [List.length_append, FreeGroup.invRev_length,
            List.length_nil] at hz
          rw [hwe]
          exact (greendlingerAtSharp_of_short_cancellation hlam ht heq
            (by omega) hi).drop_of_le hN
  | succ n ih =>
      intro e c t w N i hlen hw ht hredp hmin hi hN
      obtain ⟨P', M, B', heq, hgw, hwe⟩ :=
        exists_leading_cancellation hw hredp hmin.2.1
      rw [hwe]
      rcases le_or_gt M.length (FreeGroup.invRev c).length with hshort | hlong
      · exact (greendlingerAtSharp_of_short_cancellation hlam ht heq hshort
          hi).drop_of_le hN
      · rcases le_or_gt (M.length + i) (c.length + t.length) with hle | hgt
        · rcases hland c t e (FreeGroup.mk w) P' M B' i hmin ht hredp heq hgw
              (by omega) hi hle with harc | hlands
          · exact (harc.drop_of_le hN)
          · obtain ⟨c', t', f, A, N', i', hf, hV, ht', hredp', hminf, hi',
              hN', hMb⟩ := hlands
            have hIH := ih f c' t'
              (conjEval ((FreeGroup.mk c', t') :: f)).toWord
              (N' + (M.length - A.length)) i'
              (by omega) FreeGroup.isReduced_toWord ht' hredp'
              (by rw [FreeGroup.mk_toWord]; exact hminf) hi' (by omega)
            have hB' : B' = (conjEval e).toWord.drop M.length := by
              rw [hgw, drop_append_of_ge (FreeGroup.invRev M) M.length B'
                (le_of_eq FreeGroup.invRev_length), FreeGroup.invRev_length,
                Nat.sub_self, List.drop_zero]
            have hsuf₁ : (conjEval ((FreeGroup.mk c', t') :: f)).toWord.drop
                (N' + (M.length - A.length)) <:+ B' := by
              rw [hB', hV, drop_add N' (M.length - A.length)
                (conjEval ((FreeGroup.mk c', t') :: f)).toWord]
              exact drop_suffix_append A _ M.length
            have hsuf₂ : B' <:+ (P' ++ B').drop N := by
              have hb := drop_suffix_append P' B' N
              rwa [show N - P'.length = 0 from by omega, List.drop_zero] at hb
            exact hIH.of_suffix (hsuf₁.trans hsuf₂)
        · obtain ⟨c₂, t₂, f, D, ht₂, hredp₂, hmin₂, hf, hD⟩ :=
            exists_postJunction_drop hcyc hne
              (metricSmallCancellation_of_le hlam hmetric) hmin ht hredp heq hgw
              (by omega) (six_mul_lt_of_lam_lt hlam hi) hgt
          obtain ⟨c₃, t₃, f₃, A₃, N₃, i₃, hf₃, hV₃, ht₃, hredp₃, hmin₃, hi₃,
            hN₃, hfit₃⟩ :=
            hdeep c t c₂ t₂ e f (FreeGroup.mk w) P' M B' N i D hmin hmin₂ ht
              ht₂ hredp hredp₂ heq hgw (by omega) hi hN hgt hf hD
          have hIH := ih f₃ c₃ t₃
            (conjEval ((FreeGroup.mk c₃, t₃) :: f₃)).toWord
            (N₃ + (D + (N - P'.length) - A₃.length)) i₃
            (by omega) FreeGroup.isReduced_toWord ht₃ hredp₃
            (by rw [FreeGroup.mk_toWord]; exact hmin₃) hi₃ (by omega)
          have hcomp : B'.drop (N - P'.length)
              = (conjEval f).toWord.drop (D + (N - P'.length)) := by
            rw [hD, ← drop_add]
          have hsuf₁ : (conjEval ((FreeGroup.mk c₃, t₃) :: f₃)).toWord.drop
              (N₃ + (D + (N - P'.length) - A₃.length))
              <:+ (conjEval f).toWord.drop (D + (N - P'.length)) := by
            rw [hV₃, drop_add N₃ (D + (N - P'.length) - A₃.length)
              (conjEval ((FreeGroup.mk c₃, t₃) :: f₃)).toWord]
            exact drop_suffix_append A₃ _ (D + (N - P'.length))
          have hsuf₂ : B'.drop (N - P'.length) <:+ (P' ++ B').drop N :=
            drop_suffix_append P' B' N
          rw [hcomp] at hsuf₂
          exact hIH.of_suffix (hsuf₁.trans hsuf₂)

/-- The sharp conclusion over the composite deep landing and repaired shallow
production. -/
theorem greendlingerConclusionSharp_of_lands'
    [DecidableEq α] {R : Set (List (α × Bool))} {lam : ℚ}
    (hcyc : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r)
    (hne : ∀ r ∈ R, r ≠ []) (hlam0 : 0 < lam) (hlam : lam ≤ 1 / 6)
    (hmetric : MetricSmallCancellation R lam)
    (hdeep : DeepCompositeLandsSharp R lam)
    (hland : LandingProductionSharp' R lam) :
    GreendlingerConclusionSharp R lam := by
  intro w hw hwne hmem
  obtain ⟨n, hcount⟩ := (mem_normalClosure_iff R (FreeGroup.mk w)).mp hmem
  obtain ⟨e₀, hv₀, -, he₀⟩ :=
    (isConjProduct_iff_exists_conjExpr n (FreeGroup.mk w)).mp hcount
  obtain ⟨e, hmin⟩ := exists_isMinimalConjExpr ⟨e₀, hv₀, he₀⟩
  cases e with
  | nil =>
      exfalso
      have hb := hmin.2.1
      rw [conjEval_nil] at hb
      have h₁ : FreeGroup.mk w = FreeGroup.mk ([] : List (α × Bool)) := by
        rw [← FreeGroup.one_eq_mk]
        exact hb.symm
      have h₂ := FreeGroup.reduce.sound h₁
      rw [hw.reduce_eq, FreeGroup.IsReduced.nil.reduce_eq] at h₂
      exact hwne h₂
  | cons _ e' =>
      obtain ⟨c, t, ht, hredp, hmin'⟩ := exists_palindromic_head hcyc hne hmin
      have htpos : 0 < t.length :=
        List.length_pos_iff.mpr (ne_nil_of_mem_symmetrization hne ht)
      have hi : ((0 : ℕ) : ℚ) < lam * (t.length : ℚ) := by
        have htq : (0 : ℚ) < (t.length : ℚ) := by exact_mod_cast htpos
        simpa using mul_pos hlam0 htq
      have harc := greendlingerAtSharp_drop_of_lands' hcyc hne hlam hmetric
        hdeep hland e'.length e' c t w 0 0 le_rfl hw ht hredp hmin' hi (by omega)
      rw [List.drop_zero] at harc
      exact greendlingerSharp_of_greendlingerAtSharp harc

/-! ## The two honest search leaves -/

/-- One sound step of the aligned cascade.  The partial-alignment invariant is
used only in the branch where the tracked position is still inside the current
survivor.  In the complementary branch the survivor is genuinely covered, so
the actual cancellation split transports the residual search to the shorter
tail. -/
theorem alignedCascadeSearch_of_partialStep [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    {V V₂ P M : List (α × Bool)} {b m m₂ : ℕ}
    (split : V = P ++ V₂.drop M.length) (decreases : m₂ < m)
    (inside : b < P.length → LandsInSharp R lam b V m)
    (next : AlignedCascadeSearch R lam V₂
      (b + M.length - P.length) m₂) :
    AlignedCascadeSearch R lam V b m := by
  by_cases hcovers : P.length ≤ b
  · exact .overrun split hcovers decreases next
  · exact .landed (inside (by omega))

/-- Deep search as a landing in a strictly shorter expression. -/
theorem deepCompositeLandsSharp_fin_two
    (R : Set (List (Fin 2 × Bool))) (lam : ℚ)
    (hcyc : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r)
    (hne : ∀ r ∈ R, r ≠ []) (hlam0 : 0 < lam) (hlam : lam ≤ 1 / 6)
    (hmetric : MetricSmallCancellation R lam) :
    DeepCompositeLandsSharp R lam := by
  intro c t c₂ t₂ e f g P' M B' N i D hmin hmin₂ ht ht₂ hredp hredp₂ heq
    htail hlow hi hN hgt hf hD
  have hmetric6 : MetricSmallCancellation R (1 / 6) :=
    metricSmallCancellation_of_le hlam hmetric
  have hi6 : 6 * i < t.length := six_mul_lt_of_lam_lt hlam hi
  have heval : conjEval ((FreeGroup.mk c₂, t₂) :: f) = conjEval e := by
    have h₁ := hmin₂.2.1
    have h₂ := hmin.2.1
    rw [conjEval_cons] at h₁ h₂
    exact mul_left_cancel (h₁.trans h₂.symm)
  have htail₂ : (conjEval ((FreeGroup.mk c₂, t₂) :: f)).toWord
      = FreeGroup.invRev M ++ B' := by
    rw [heval]
    exact htail
  have hover : ¬(FreeGroup.invRev M <+: palindrome c₂ t₂) := by
    rintro ⟨B₂, hB₂⟩
    exact not_deep_confined hne hmetric6 hmin₂ ht ht₂ hredp hredp₂ heq
      hB₂.symm hlow hi6 hgt
  have hfne : f ≠ [] := tail_ne_nil_of_nonConfined hredp₂ htail₂ hover
  cases f with
  | nil => exact absurd rfl hfne
  | cons x f₃ =>
      obtain ⟨x₃, s₃⟩ := x
      obtain ⟨c₃, t₃, ht₃, hredp₃, hmin₃⟩ :=
        exists_palindromic_thd hcyc hne hmin₂
      obtain ⟨P₃, M₃, B₃, hpal₃, htail₃, hstep₃⟩ :=
        exists_tail_step_word (f := f₃) hredp₃
      have hshort : f₃.length < ((x₃, s₃) :: f₃).length := by
        simp only [List.length_cons]
        omega
      have heval₃ : conjEval ((FreeGroup.mk c₃, t₃) :: f₃)
          = conjEval ((x₃, s₃) :: f₃) := by
        have h₁ := hmin₃.2.1
        have h₂ := hmin₂.2.1
        rw [conjEval_cons, conjEval_cons] at h₁ h₂
        have htailEq := mul_left_cancel (h₁.trans h₂.symm)
        exact mul_left_cancel htailEq
      have hword₃ : (conjEval ((x₃, s₃) :: f₃)).toWord
          = (conjEval ((FreeGroup.mk c₃, t₃) :: f₃)).toWord := by
        rw [heval₃]
      rw [hword₃]
      let b : ℕ := D + (N - P'.length)
      change LandsInSharp R lam b
        (conjEval ((FreeGroup.mk c₃, t₃) :: f₃)).toWord
        ((x₃, s₃) :: f₃).length
      have ht₃pos : 0 < t₃.length :=
        List.length_pos_iff.mpr (ne_nil_of_mem_symmetrization hne ht₃)
      rcases le_or_gt b c₃.length with hburied | hrotation
      · exact landsInSharp_of_confined (i := 0) ht₃ hredp₃ hmin₃.tail.tail
          (cast_zero_lt_lam_mul hlam0 ht₃pos) hburied hshort
      · let q : ℕ := b - c₃.length
        by_cases hq : (q : ℚ) < lam * (t₃.length : ℚ)
        · exact landsInSharp_of_confined (i := q) ht₃ hredp₃ hmin₃.tail.tail
            hq (by dsimp [q]; omega) hshort
        · have hdrop₃ : B₃ = (conjEval f₃).toWord.drop M₃.length := by
            symm
            exact drop_invRev_block htail₃
          have hsplit₃ :
              (conjEval ((FreeGroup.mk c₃, t₃) :: f₃)).toWord =
                P₃ ++ (conjEval f₃).toWord.drop M₃.length := by
            rw [hstep₃, ← hdrop₃]
          -- This is the sole deep search leaf.  In the inside-survivor branch
          -- the partial-alignment state supplies the current landing; in the
          -- complementary branch it is transported to the strictly shorter
          -- tail.  Coverage is then derived by the sound step combinator,
          -- rather than demanded without provenance.
          obtain ⟨hinside, hnext⟩ :
              (b < P₃.length → LandsInSharp R lam b
                (conjEval ((FreeGroup.mk c₃, t₃) :: f₃)).toWord
                ((x₃, s₃) :: f₃).length) ∧
                AlignedCascadeSearch R lam (conjEval f₃).toWord
                  (b + M₃.length - P₃.length) f₃.length := by
            sorry
          have hsearch : AlignedCascadeSearch R lam
              (conjEval ((FreeGroup.mk c₃, t₃) :: f₃)).toWord b
              ((x₃, s₃) :: f₃).length :=
            alignedCascadeSearch_of_partialStep hsplit₃ hshort hinside hnext
          exact landsInSharp_of_alignedCascadeSearch hlam hmetric hsearch

/-- Repaired shallow production from the aligned non-confined cursor search. -/
theorem landingProductionBetaSharp'_fin_two
    (R : Set (List (Fin 2 × Bool))) (lam : ℚ)
    (hcyc : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r)
    (hne : ∀ r ∈ R, r ≠ []) (hlam0 : 0 < lam) (hlam : lam ≤ 1 / 6)
    (hmetric : MetricSmallCancellation R lam) :
    LandingProductionBetaSharp' R lam :=
  landingProductionBetaSharp'_of_largeSegmentLands hlam
    (largeSegmentLands_of_nonConfined hcyc hne hlam0 hlam hmetric
      (nonConfinedBlockLands_fin_two_of_progress R lam hcyc hne hlam0 hlam
        hmetric))

/-- Nondegenerate sharp conclusion family on the router alphabet. -/
theorem greendlingerConclusionSharp_fin_two
    (R : Set (List (Fin 2 × Bool))) (lam : ℚ)
    (hcyc : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r)
    (hne : ∀ r ∈ R, r ≠ []) (hlam0 : 0 < lam) (hlam : lam ≤ 1 / 6)
    (hmetric : MetricSmallCancellation R lam) :
    GreendlingerConclusionSharp R lam :=
  greendlingerConclusionSharp_of_lands' hcyc hne hlam0 hlam hmetric
    (deepCompositeLandsSharp_fin_two R lam hcyc hne hlam0 hlam hmetric)
    (landingProductionSharp'_of_betaSharp' hmetric
      (landingProductionBetaSharp'_fin_two R lam hcyc hne hlam0 hlam hmetric))

/-- Premise-free sharp gate used by the two-generator router. -/
theorem sharpGreendlingerGate_fin_two :
    GreendlingerFreeGate.SharpGreendlingerGate (Fin 2) := by
  intro R lam hcyc hlam hmetric
  by_cases hex : ∃ r ∈ R, r ≠ []
  · obtain ⟨s₁, hs₁, s₂, hs₂, hdistinct⟩ :=
      exists_two_distinct_symmetrization hcyc hex
    obtain ⟨r, hr, hrne⟩ := hex
    have hlam0 : 0 < lam :=
      lam_pos_of_metric hmetric hs₁ hs₂ hdistinct (subset_symmetrization R hr)
        hrne
    have hne : ∀ q ∈ R, q ≠ [] := fun q hq =>
      ne_nil_of_metric_lam hmetric hs₁ hs₂ hdistinct
        (subset_symmetrization R hq)
    exact greendlingerConclusionSharp_fin_two R lam hcyc hne hlam0 hlam hmetric
  · intro w hw hwne hmem
    exfalso
    push Not at hex
    have hsub : FreeGroup.mk '' R ⊆
        ((⊥ : Subgroup (FreeGroup (Fin 2))) : Set (FreeGroup (Fin 2))) := by
      rintro _ ⟨r, hr, rfl⟩
      have hone : FreeGroup.mk r = (1 : FreeGroup (Fin 2)) := by
        rw [hex r hr, ← FreeGroup.one_eq_mk]
      simp [hone]
    have hb := Subgroup.normalClosure_le_normal hsub hmem
    rw [Subgroup.mem_bot] at hb
    have h₁ : FreeGroup.mk w = FreeGroup.mk ([] : List (Fin 2 × Bool)) := by
      rw [hb]
      exact FreeGroup.one_eq_mk
    have h₂ := FreeGroup.reduce.sound h₁
    rw [hw.reduce_eq, FreeGroup.IsReduced.nil.reduce_eq] at h₂
    exact hwne h₂

end SmallCancellationRouter
end GroupApproximation
