import GroupApproximation.GGT.DGOLemma421MatchPositionBounds
import GroupApproximation.GGT.DGOLemma421MinimalGap

/-!
# Two separated forward matches from the counting certificate

The early window bounds the first target position. A sufficiently late window
then forces a larger target position by quasi-geodesicity. This supplies the
forward endpoints needed by the minimal-gap argument, while retaining a
prescribed source rank gap.
-/

namespace GroupApproximation.GGT.OsinComponents

open GroupApproximation.WordMetric

universe u w
variable {G : Type u} [Group G] {Lambda : Type w}

/-- The located counting certificate contains forward matched endpoints far
enough apart to support a length-`K` consecutive block. -/
theorem DGO421LocatedAbsorptionCertificate.exists_forward_matches
    {D : RelGenSet G Lambda} {P Q : List (RelLetter G Lambda)} {N M B : ℕ}
    (cert : DGO421LocatedAbsorptionCertificate D P Q N M B) {vp vq : G} {E K : ℕ}
    (hpre : cert.pre = vq⁻¹ * vp)
    (hletP : ∀ letter ∈ P, D.IsLetter letter) (hletQ : ∀ letter ∈ Q, D.IsLetter letter)
    (hW1P : WWord.IsWOne P)
    (hstart : (wordDist D.alphabet.carrier vp vq : ℝ) ≤ E)
    (hqgP : ∀ a b : ℕ, a ≤ b → b ≤ P.length →
      ((b - a : ℕ) : ℝ) / 4 - 1 ≤
        (wordDist D.alphabet.carrier (vertex vp P a) (vertex vp P b) : ℝ))
    (hqgQ : ∀ a b : ℕ, a ≤ b → b ≤ Q.length →
      ((b - a : ℕ) : ℝ) / 4 - 1 ≤
        (wordDist D.alphabet.carrier (vertex vq Q a) (vertex vq Q b) : ℝ))
    (hsize : 32 * M + 20 * E + K + 89 + M < N) :
    ∃ s t : Fin (peripheralPositions P).card,
    ∃ a b : Fin (peripheralPositions Q).card,
      s < t ∧ a < b ∧ K ≤ t.val - s.val + 1 ∧
      (peripheralOccurrence Q a).label = (peripheralOccurrence P s).label ∧
      (peripheralOccurrence Q b).label = (peripheralOccurrence P t).label ∧
      (vertex vp P (peripheralOccurrence P s).pos)⁻¹ *
        vertex vq Q (peripheralOccurrence Q a).pos ∈ D.fam (peripheralOccurrence P s).label ∧
      (vertex vp P (peripheralOccurrence P t).pos)⁻¹ *
        vertex vq Q (peripheralOccurrence Q b).pos ∈ D.fam (peripheralOccurrence P t).label := by
  let lo := 32 * M + 20 * E + K + 89
  obtain ⟨i, _, hi, himatch⟩ := cert.exists_match_in_window 0 (by omega)
  obtain ⟨j, hj, _, hjmatch⟩ := cert.exists_match_in_window lo hsize
  obtain ⟨a, halabel, hamatch⟩ :=
    cert.toDGO421FiniteAbsorptionCertificate.matched_rank hpre hletQ i himatch
  obtain ⟨b, hblabel, hbmatch⟩ :=
    cert.toDGO421FiniteAbsorptionCertificate.matched_rank hpre hletQ j hjmatch
  have hsourceI := cert.source_bounds hW1P i
  have hsourceJ := cert.source_bounds hW1P j
  have hiBound : (peripheralOccurrence P (cert.rank i)).pos ≤ P.length := by
    rw [cert.rank_pos]
    have := (cert.source_comp i).2.1
    omega
  have hjBound : (peripheralOccurrence P (cert.rank j)).pos ≤ P.length := by
    rw [cert.rank_pos]
    have := (cert.source_comp j).2.1
    omega
  have haBound : (peripheralOccurrence Q a).pos ≤ Q.length :=
    Nat.le_of_lt (List.getElem?_eq_some_iff.mp (peripheralOccurrence Q a).read).1
  have hbBound : (peripheralOccurrence Q b).pos ≤ Q.length :=
    Nat.le_of_lt (List.getElem?_eq_some_iff.mp (peripheralOccurrence Q b).read).1
  have hgap : 16 * (peripheralOccurrence P (cert.rank i)).pos + 20 * E + 40 <
      (peripheralOccurrence P (cert.rank j)).pos := by
    rw [cert.rank_pos, cert.rank_pos]
    dsimp [lo] at hj
    omega
  have habpos := target_position_lt_of_separated_source_matches hletP hletQ
    hiBound hjBound haBound hbBound hstart hqgP hqgQ hamatch hbmatch hgap
  have hab := peripheralOccurrence_rank_lt_of_pos_lt Q habpos
  have hN : 0 < N := by omega
  have hri := cert.toDGO421FiniteAbsorptionCertificate.rank_formula hN i
  have hrj := cert.toDGO421FiniteAbsorptionCertificate.rank_formula hN j
  refine ⟨cert.rank i, cert.rank j, a, b, ?_, hab, ?_, halabel, hblabel, hamatch, hbmatch⟩
  · change (cert.rank i).val < (cert.rank j).val
    dsimp [lo] at hj
    omega
  · dsimp [lo] at hj
    omega

end GroupApproximation.GGT.OsinComponents

#audit_axioms GroupApproximation.GGT.OsinComponents.DGO421LocatedAbsorptionCertificate.exists_forward_matches
