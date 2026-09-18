import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauFix3VacFlexB
import GroupApproximation.Meta.AxiomGuard

/-!
# The unequal-length case (lane bh-met-92x)

* `higmanVCTauFix3Vac_pq`: the configuration `(p u, q v) ↦ (q u, p v)` off the cross family;
* `higmanVCTauFix3Vac_ff`: both words fixed, not both short;
* `higmanVCTauFix3Vac_flexB`: flexible B from the hypotheses of the rest statement, for
  `|p| ≠ |q|`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **The swapped configuration** `(p u, q v) ↦ (q u, p v)`, off the cross family. -/
theorem higmanVCTauFix3Vac_pq {d : ℕ} (hd : 1 < d) {p q : List (Fin d)} (u v : List (Fin d))
    (hpq : ¬ p <+: q) (hqp : ¬ q <+: p) (hl : p.length ≠ q.length) (hp3 : p.length ≤ 3)
    (hq3 : q.length ≤ 3) (hC : ¬ higmanVCTauDecomp_Cross p q (p ++ u) (q ++ v))
    (hC' : ¬ higmanVCTauDecomp_Cross q p (p ++ u) (q ++ v)) :
    higmanVCTauComm_FlexB d p q (p ++ u) (q ++ v) (q ++ u) (p ++ v) := by
  have hp0 : p.length ≠ 0 := fun h =>
    hpq (Eq.subst (motive := fun w => w <+: q) (List.eq_nil_of_length_eq_zero h).symm
      List.nil_prefix)
  have hq0 : q.length ≠ 0 := fun h =>
    hqp (Eq.subst (motive := fun w => w <+: p) (List.eq_nil_of_length_eq_zero h).symm
      List.nil_prefix)
  by_cases h3 : p.length = 3
  · exact higmanVCTauFix3Vac_fbL hd hpq hqp h3 (by omega) u v
  by_cases h3' : q.length = 3
  · exact higmanVCTauFix3Vac_fbSwapPQ
      (higmanVCTauFix3Vac_fbSwapXY (higmanVCTauFix3Vac_fbL hd hqp hpq h3' (by omega) v u))
  exfalso
  have hpu := List.prefix_append p u
  have hqv := List.prefix_append q v
  by_cases h1 : p.length = 1
  · apply hC
    unfold higmanVCTauDecomp_Cross
    exact ⟨h1, by omega, Or.inl ⟨hpu, hqv⟩⟩
  · apply hC'
    unfold higmanVCTauDecomp_Cross
    exact ⟨by omega, by omega, Or.inr ⟨hqv, hpu⟩⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauFix3Vac_pq

/-- **Both words fixed**, not both short. -/
theorem higmanVCTauFix3Vac_ff {d : ℕ} (hd : 1 < d) {p q x y x' y' : List (Fin d)}
    (hpq : ¬ p <+: q) (hqp : ¬ q <+: p) (hl : p.length ≠ q.length) (hp3 : p.length ≤ 3)
    (hq3 : q.length ≤ 3)
    (hs : ¬ (x.length ≤ 3 ∧ y.length ≤ 3 ∧ x'.length ≤ 3 ∧ y'.length ≤ 3))
    (hmx : MapsCone (coneSwap p q hpq hqp) x x') (hmy : MapsCone (coneSwap p q hpq hqp) y y')
    (hxy : ¬ x <+: y) (hyx : ¬ y <+: x) (hx0 : ¬ p <+: x ∧ ¬ q <+: x)
    (hy0 : ¬ p <+: y ∧ ¬ q <+: y) (hxe : x' = x) (hye : y' = y) :
    higmanVCTauComm_FlexB d p q x y x' y' := by
  have hxi := higmanVCTauFix3Vac_incOf hd hpq hqp hmx hx0.1 hx0.2
  have hyi := higmanVCTauFix3Vac_incOf hd hpq hqp hmy hy0.1 hy0.2
  rw [hxe, hye]
  rw [hxe, hye] at hs
  by_cases hx3 : 3 ≤ x.length
  · obtain ⟨t, r, hm, ht⟩ := higmanVCTauFix3_split3 hx3
    rcases Nat.lt_or_gt_of_ne hl with h | h
    · exact higmanVCTauFix3Vac_fbFF hpq hqp (by omega) hq3 hm ht hx0.1 hx0.2 hyi.1 hyx
    · exact higmanVCTauFix3Vac_fbSwapPQ
        (higmanVCTauFix3Vac_fbFF hqp hpq (by omega) hp3 hm ht hx0.2 hx0.1 hyi.2 hyx)
  · have hy3 : 3 ≤ y.length := by omega
    obtain ⟨t, r, hm, ht⟩ := higmanVCTauFix3_split3 hy3
    rcases Nat.lt_or_gt_of_ne hl with h | h
    · exact higmanVCTauFix3Vac_fbSwapXY
        (higmanVCTauFix3Vac_fbFF hpq hqp (by omega) hq3 hm ht hy0.1 hy0.2 hxi.1 hxy)
    · exact higmanVCTauFix3Vac_fbSwapXY (higmanVCTauFix3Vac_fbSwapPQ
        (higmanVCTauFix3Vac_fbFF hqp hpq (by omega) hp3 hm ht hy0.2 hy0.1 hxi.2 hxy))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauFix3Vac_ff

/-- **Flexible B in the unequal-length case**, from the hypotheses of the rest statement. -/
theorem higmanVCTauFix3Vac_flexB {d : ℕ} (hd : 1 < d) {p q x y x' y' : List (Fin d)}
    (hpq : ¬ p <+: q) (hqp : ¬ q <+: p) (hl : p.length ≠ q.length) (hp3 : p.length ≤ 3)
    (hq3 : q.length ≤ 3) (hC : ¬ higmanVCTauDecomp_Cross p q x y)
    (hC' : ¬ higmanVCTauDecomp_Cross q p x y)
    (hn : x.length + y.length = x'.length + y'.length)
    (hs : ¬ (x.length ≤ 3 ∧ y.length ≤ 3 ∧ x'.length ≤ 3 ∧ y'.length ≤ 3))
    (hmx : MapsCone (coneSwap p q hpq hqp) x x') (hmy : MapsCone (coneSwap p q hpq hqp) y y')
    (hxy : ¬ x <+: y) (hyx : ¬ y <+: x) :
    higmanVCTauComm_FlexB d p q x y x' y' := by
  rcases higmanVCTauFix3Vac_cls hd hpq hqp hmx with ⟨u, rfl, rfl⟩ | ⟨u, rfl, rfl⟩ | ⟨hx0, hxe⟩ <;>
    rcases higmanVCTauFix3Vac_cls hd hpq hqp hmy with ⟨v, rfl, rfl⟩ | ⟨v, rfl, rfl⟩ | ⟨hy0, hye⟩
  · exfalso
    simp only [List.length_append] at hn <;> omega
  · exact higmanVCTauFix3Vac_pq hd u v hpq hqp hl hp3 hq3 hC hC'
  · exfalso
    rw [hye] at hn
    simp only [List.length_append] at hn <;> omega
  · exact higmanVCTauFix3Vac_fbSwapXY (higmanVCTauFix3Vac_pq hd v u hpq hqp hl hp3 hq3
      (fun h => hC (higmanVCTauFix3Vac_crossSwap h))
      (fun h => hC' (higmanVCTauFix3Vac_crossSwap h)))
  · exfalso
    simp only [List.length_append] at hn <;> omega
  · exfalso
    rw [hye] at hn
    simp only [List.length_append] at hn <;> omega
  · exfalso
    rw [hxe] at hn
    simp only [List.length_append] at hn <;> omega
  · exfalso
    rw [hxe] at hn
    simp only [List.length_append] at hn <;> omega
  · exact higmanVCTauFix3Vac_ff hd hpq hqp hl hp3 hq3 hs hmx hmy hxy hyx hx0 hy0 hxe hye

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauFix3Vac_flexB

end GroupApproximation.BooneHigman.Metabelian.Envelope
