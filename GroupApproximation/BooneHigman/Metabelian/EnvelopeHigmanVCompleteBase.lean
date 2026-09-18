import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCompleteShort
import GroupApproximation.Meta.AxiomGuard

/-!
# The short standard relators are killed by every `ψ_τ` (lane bh-met-77b)

For every choice `τ` of values on the long pairs, `ψ_τ` kills every standard relator
`higmanVC_rels d P` with `P l := l.length ≤ 3` (`higmanVC_psi_short`): these relators are sent
to classes of the letter relators `higmanVFP_letter_comparable_mem`, `higmanVFP_letter_sq_mem`,
`higmanVFP_letter_conj_mem` and `higmanVFP_letter_split_mem` of lane bh-met-77.  This is the base
case of the transfer; only relators involving a word of length `≥ 4` remain.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- `ψ_τ` sends the all-swaps split word of a pair of words of length `≤ 2` to the class of the
short split word. -/
theorem higmanVC_psi_splitAll {d : ℕ} (τ : List (Fin d) × List (Fin d) → higmanVC_Q d)
    {v w : List (Fin d)} (hv : v.length ≤ 2) (hw : w.length ≤ 2) :
    higmanVC_psi d τ (higmanVC_splitAll v w) = higmanVC_mk d (higmanVFPSplitWord hv hw) := by
  rw [higmanVC_splitAll, higmanVFPSplitWord, map_list_prod, map_list_prod, List.map_map,
    List.map_map]
  congr 1
  refine List.map_congr_left fun a _ => ?_
  exact higmanVC_psi_of_short τ (higmanVFP_len_succ hv a) (higmanVFP_len_succ hw a)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVC_psi_splitAll

/-- A word whose one-letter extension has length `≤ 3` has length `≤ 2`. -/
theorem higmanVC_len_le2 {d : ℕ} {v : List (Fin d)} {a : Fin d} (h : (v ++ [a]).length ≤ 3) :
    v.length ≤ 2 := by
  rw [List.length_append, List.length_singleton] at h
  omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVC_len_le2

/-- **Base case.**  Every standard relator all of whose words have length `≤ 3` is killed by
`ψ_τ`, whatever `τ` is. -/
theorem higmanVC_psi_short {d : ℕ} (τ : List (Fin d) × List (Fin d) → higmanVC_Q d)
    (hd : 0 < d) {t : FreeGroup (List (Fin d) × List (Fin d))}
    (ht : t ∈ higmanVC_rels d fun l => l.length ≤ 3) : higmanVC_psi d τ t = 1 := by
  rcases ht with ⟨v, w, hv, hw, hc, rfl⟩ | ⟨v, w, hv, hw, rfl⟩ |
      ⟨p, q, x, y, x', y', hp, hq, hx, hy, hx', hy', hpq, hqp, hmx, hmy, hxy, hyx, hxy', hyx',
        rfl⟩ |
      ⟨v, w, _, _, hs, h1, h2, rfl⟩
  · rw [higmanVC_psi_of_short τ hv hw]
    exact higmanVC_mk_rel (higmanVFP_letter_comparable_mem hv hw hc)
  · have h := higmanVC_mk_rel (higmanVFP_letter_sq_mem hv hw)
    rw [map_mul] at h ⊢
    rw [higmanVC_psi_of_short τ hv hw]
    exact h
  · have h := higmanVC_mk_rel (higmanVFP_letter_conj_mem hp hq hx hy hx' hy' hpq hqp hxy hyx
      hxy' hyx' hmx hmy)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h ⊢
    rw [higmanVC_psi_of_short τ hp hq, higmanVC_psi_of_short τ hx hy,
      higmanVC_psi_of_short τ hx' hy']
    exact h
  · have hv2 : v.length ≤ 2 := higmanVC_len_le2 (hs ⟨0, hd⟩).1
    have hw2 : w.length ≤ 2 := higmanVC_len_le2 (hs ⟨0, hd⟩).2
    have h := higmanVC_mk_rel (higmanVFP_letter_split_mem hv2 hw2 h1 h2)
    rw [map_mul, map_inv] at h ⊢
    rw [higmanVC_psi_of_short τ (higmanVFP_len_le3 hv2) (higmanVFP_len_le3 hw2),
      higmanVC_psi_splitAll τ hv2 hw2]
    exact h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVC_psi_short

end GroupApproximation.BooneHigman.Metabelian.Envelope
