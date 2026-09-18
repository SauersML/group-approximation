import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauSplitWords
import GroupApproximation.Meta.AxiomGuard

/-!
# Incomparability, lengths and appending stability of the descent (lane bh-met-77f)

For a main word `m` with `3 ≤ |m|` and an incomparable other word `o`:

* `dM m o`, `dO m o` are incomparable (`higmanVCTauSplit_incomp_desc`);
* `|dM m o| < |m|` and `|dO m o| ≤ |o|` (`higmanVCTauSplit_len_desc`);
* appending a letter `a` to both words leaves `descP` (and `take 3`) unchanged and appends `a`
  to `dM` and `dO` (`higmanVCTauSplit_descP_append`, `higmanVCTauSplit_dM_append`,
  `higmanVCTauSplit_dO_append`).

Machine-checked first in `scratchpad/bh-met-77f/split_check.py`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- The descended words are incomparable. -/
theorem higmanVCTauSplit_incomp_desc {d : ℕ} {m o : List (Fin d)} (hmo : ¬ m <+: o)
    (hom : ¬ o <+: m) (hPo : ¬ higmanVCTau_descP m o <+: o)
    (hoP : ¬ o <+: higmanVCTau_descP m o) (hm : 3 ≤ m.length) :
    ¬ higmanVCTau_dM m o <+: higmanVCTau_dO m o ∧
      ¬ higmanVCTau_dO m o <+: higmanVCTau_dM m o := by
  unfold higmanVCTau_dM higmanVCTau_dO
  split_ifs with h
  · obtain ⟨s, hs⟩ := h
    have hl : (m.take 3).length = 3 := by
      rw [List.length_take]
      omega
    rw [higmanVCTauSplit_drop_of_prefix hs hl]
    have hm' : m.take 3 ++ m.drop 3 = m := List.take_append_drop 3 m
    refine ⟨fun h => hmo ?_, fun h => hom ?_⟩
    · have h' := (List.prefix_append_right_inj (m.take 3)).mpr
        ((List.prefix_append_right_inj _).mp h)
      rw [hm', hs] at h'
      exact h'
    · have h' := (List.prefix_append_right_inj (m.take 3)).mpr
        ((List.prefix_append_right_inj _).mp h)
      rw [hm', hs] at h'
      exact h'
  · exact ⟨vgen_not_prefix_append_left _ hPo, vgen_not_prefix_append_right _ hPo hoP⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauSplit_incomp_desc

/-- The descent shortens the main word and does not lengthen the other word. -/
theorem higmanVCTauSplit_len_desc {d : ℕ} (hd : 1 < d) {m o : List (Fin d)}
    (hom : ¬ o <+: m) (hm : 3 ≤ m.length) :
    (higmanVCTau_dM m o).length < m.length ∧ (higmanVCTau_dO m o).length ≤ o.length := by
  have hP := (higmanVCTauSplit_descP_facts hd hom hm).2.2
  refine ⟨?_, ?_⟩
  · rw [higmanVCTau_dM, List.length_append, List.length_drop]
    omega
  · unfold higmanVCTau_dO
    split_ifs with h
    · have hl := h.length_le
      rw [List.length_take] at hl
      rw [List.length_append, List.length_drop]
      omega
    · exact le_refl _

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauSplit_len_desc

/-- Appending a letter to both words does not change `descP`. -/
theorem higmanVCTauSplit_descP_append {d : ℕ} {m o : List (Fin d)} (hom : ¬ o <+: m)
    (hm : 3 ≤ m.length) (a : Fin d) :
    higmanVCTau_descP (m ++ [a]) (o ++ [a]) = higmanVCTau_descP m o := by
  obtain ⟨x, y, z, r, rfl⟩ := higmanVCTauSplit_three hm
  obtain ⟨e, os, rfl⟩ := higmanVCTauSplit_ne_nil hom
  simp only [List.cons_append, higmanVCTauSplit_descP_cons, List.head?_cons]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauSplit_descP_append

/-- Appending a letter to both words appends it to the descended main word. -/
theorem higmanVCTauSplit_dM_append {d : ℕ} {m o : List (Fin d)} (hom : ¬ o <+: m)
    (hm : 3 ≤ m.length) (a : Fin d) :
    higmanVCTau_dM (m ++ [a]) (o ++ [a]) = higmanVCTau_dM m o ++ [a] := by
  unfold higmanVCTau_dM
  rw [higmanVCTauSplit_descP_append hom hm, List.drop_append_of_le_length hm, List.append_assoc]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauSplit_dM_append

/-- `take 3 m` is a prefix of `o ++ [a]` iff it is a prefix of `o` (as `o` is not a prefix
of `m`). -/
theorem higmanVCTauSplit_take_prefix_append {d : ℕ} {m o : List (Fin d)} (hom : ¬ o <+: m)
    (hm : 3 ≤ m.length) (a : Fin d) : m.take 3 <+: o ++ [a] ↔ m.take 3 <+: o := by
  refine ⟨fun h => ?_, fun h => h.trans (List.prefix_append o [a])⟩
  by_cases ho : 3 ≤ o.length
  · exact List.prefix_of_prefix_length_le h (List.prefix_append o [a])
      (by rw [List.length_take]; omega)
  · exact absurd ((List.prefix_of_prefix_length_le (List.prefix_append o [a]) h
      (by rw [List.length_take]; omega)).trans (List.take_prefix 3 m)) hom

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauSplit_take_prefix_append

/-- Appending a letter to both words appends it to the descended other word. -/
theorem higmanVCTauSplit_dO_append {d : ℕ} {m o : List (Fin d)} (hom : ¬ o <+: m)
    (hm : 3 ≤ m.length) (a : Fin d) :
    higmanVCTau_dO (m ++ [a]) (o ++ [a]) = higmanVCTau_dO m o ++ [a] := by
  have hT : (m ++ [a]).take 3 = m.take 3 := List.take_append_of_le_length hm
  have hiff := higmanVCTauSplit_take_prefix_append hom hm a
  unfold higmanVCTau_dO
  rw [higmanVCTauSplit_descP_append hom hm]
  by_cases h2 : m.take 3 <+: o
  · have h1 : (m ++ [a]).take 3 <+: o ++ [a] := by
      rw [hT]
      exact hiff.mpr h2
    have h3 : 3 ≤ o.length := by
      have hl := h2.length_le
      rw [List.length_take] at hl
      omega
    rw [if_pos h1, if_pos h2, List.drop_append_of_le_length h3, List.append_assoc]
  · have h1 : ¬ (m ++ [a]).take 3 <+: o ++ [a] := by
      rw [hT]
      exact fun h => h2 (hiff.mp h)
    rw [if_neg h1, if_neg h2]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauSplit_dO_append

end GroupApproximation.BooneHigman.Metabelian.Envelope
