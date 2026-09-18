import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauDecompWordsS
import GroupApproximation.Meta.AxiomGuard

/-!
# Form `sas` decompositions of the swapped cross family (lane bh-met-91w)

The swapped cross family: `s = ([α], [β γ])` with `α ≠ β`, `x = β γ v`, `y = α u`.  Then
`x' = α v` and `y' = β γ u`.  This is `EnvelopeHigmanVCTauDecompCross` with the two words of
every pair read in the other order.  Let `g ≠ γ` (and `w0 ≠ v0`) be letters.

* `higmanVCTauDecomp_crossNeS` (`v = v0 v'`): form `sas` with `a = ([β g], [β γ v0])`,
  `c = ([β g], [α v0])`, `A1 = (β g v', α u)`, `A2 = (β g v', β γ u)`.  The first two
  sub-instances are one level below `n`.  The third is at level `n`, by flexible A
  (`higmanVCTauDecomp_flexUS`, `higmanVCTauDecomp_flexES`).  `u = v' = []` is all short.
* `higmanVCTauDecomp_crossNilS` (`v = []`, `u = u0 u1 r`): form `sas` with
  `a = ([α u0], [β g])`, `c = ([β γ u0], [β g])`, `A1 = (β γ, β g u1 r)`,
  `A2 = (α, β g u1 r)`.  The first sub-instance is all short (`r = []`) or option A at level
  `n` (`higmanVCTauDecomp_optAS`).  The other two are one level below `n`.

No negated-option hypothesis is used: the decompositions exist for every such instance.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **Swapped cross family, `v = v0 v'`.**  A form `sas` decomposition. -/
theorem higmanVCTauDecomp_crossNeS {d n : ℕ} (hd : 1 < d) {α β γ v0 : Fin d}
    (u v' : List (Fin d)) (hαβ : α ≠ β) (hpq : ¬ [α] <+: [β, γ]) (hqp : ¬ [β, γ] <+: [α])
    (hn : (β :: γ :: v0 :: v').length + (α :: u).length = n)
    (hns : ¬ ((β :: γ :: v0 :: v').length ≤ 3 ∧ (α :: u).length ≤ 3 ∧
      (α :: v0 :: v').length ≤ 3 ∧ (β :: γ :: u).length ≤ 3)) :
    higmanVCTauEqTwo_Sas d n [α] [β, γ] (β :: γ :: v0 :: v') (α :: u) (α :: v0 :: v')
      (β :: γ :: u) hpq hqp := by
  obtain ⟨g, hg⟩ : ∃ g : Fin d, g ≠ γ := ⟨_, higmanVCTauSplit_other_ne hd γ⟩
  obtain ⟨w0, hw⟩ : ∃ w0 : Fin d, w0 ≠ v0 := ⟨_, higmanVCTauSplit_other_ne hd v0⟩
  have ha := higmanVCTauD2_inc2 (e := β) [] [v0] hg
  have hc := higmanVCTauBridge_inc_cons [g] [v0] hαβ.symm
  have hFA : higmanVCTauComm_FlexA d [β, g] [α, v0] (β :: g :: v') (β :: γ :: u) hc.1 hc.2 := by
    rcases u with _ | ⟨u0, u⟩
    · rcases v' with _ | ⟨v1, v''⟩
      · exact (hns ⟨by simp, by simp, by simp, by simp⟩).elim
      · exact higmanVCTauDecomp_flexES v'' hαβ hg hw hc.1 hc.2
    · exact higmanVCTauDecomp_flexUS u v' hαβ hg hw hc.1 hc.2
  unfold higmanVCTauEqTwo_Sas
  refine ⟨[β, g], [β, γ, v0], [β, g], [α, v0], β :: g :: v', α :: u, β :: g :: v', β :: γ :: u,
    ha.1, ha.2, hc.1, hc.2, by simp, by simp, by simp, by simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · exact higmanVCTauD2_fix hpq hqp (higmanVCTauBridge_inc_cons [g] [] hαβ.symm)
      (higmanVCTauD2_inc2 (e := β) [] [] hg)
  · exact (mapsCone_coneSwap_right hpq hqp).append [v0]
  · exact (mapsCone_coneSwap_right ha.1 ha.2).append v'
  · exact higmanVCTauD2_fix ha.1 ha.2 (higmanVCTauBridge_inc_cons u [g] hαβ)
      (higmanVCTauBridge_inc_cons u [γ, v0] hαβ)
  · exact higmanVCTauD2_fix hpq hqp (higmanVCTauBridge_inc_cons (g :: v') [] hαβ.symm)
      (higmanVCTauD2_inc2 (e := β) v' [] hg)
  · exact (mapsCone_coneSwap_left hpq hqp).append u
  · exact (mapsCone_coneSwap_left hc.1 hc.2).append v'
  · exact higmanVCTauD2_fix hc.1 hc.2 (higmanVCTauD2_inc2 (e := β) u [] hg.symm)
      (higmanVCTauBridge_inc_cons (γ :: u) [v0] hαβ.symm)
  · unfold higmanVCTauEqTwo_Known
    refine Or.inr (Or.inl ⟨?_, ?_⟩) <;> simp only [List.length_cons] at hn ⊢ <;> omega
  · unfold higmanVCTauEqTwo_Known
    refine Or.inl ⟨?_, ?_⟩ <;> simp only [List.length_cons] at hn ⊢ <;> omega
  · unfold higmanVCTauEqTwo_Known higmanVCTauEqTwo_Opt
    refine Or.inr (Or.inr (Or.inr ⟨?_, ?_, Or.inl (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨hc.1, hc.2, hFA⟩))))⟩)) <;> simp only [List.length_cons] at hn ⊢ <;> omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauDecomp_crossNeS

/-- **Swapped cross family, `v = []`, `u = u0 u1 r`.**  A form `sas` decomposition. -/
theorem higmanVCTauDecomp_crossNilS {d n : ℕ} (hd : 1 < d) {α β γ u0 u1 : Fin d}
    (r : List (Fin d)) (hαβ : α ≠ β) (hpq : ¬ [α] <+: [β, γ]) (hqp : ¬ [β, γ] <+: [α])
    (hn : [β, γ].length + (α :: u0 :: u1 :: r).length = n) :
    higmanVCTauEqTwo_Sas d n [α] [β, γ] [β, γ] (α :: u0 :: u1 :: r) [α]
      (β :: γ :: u0 :: u1 :: r) hpq hqp := by
  obtain ⟨g, hg⟩ : ∃ g : Fin d, g ≠ γ := ⟨_, higmanVCTauSplit_other_ne hd γ⟩
  have ha := higmanVCTauBridge_inc_cons [u0] [g] hαβ
  have hc := higmanVCTauD2_inc2 (e := β) [u0] [] hg.symm
  unfold higmanVCTauEqTwo_Sas
  refine ⟨[α, u0], [β, g], [β, γ, u0], [β, g], [β, γ], β :: g :: u1 :: r, [α],
    β :: g :: u1 :: r, ha.1, ha.2, hc.1, hc.2, by simp, by simp, by simp, by simp, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (mapsCone_coneSwap_left hpq hqp).append [u0]
  · exact higmanVCTauD2_fix hpq hqp (higmanVCTauBridge_inc_cons [g] [] hαβ.symm)
      (higmanVCTauD2_inc2 (e := β) [] [] hg)
  · exact higmanVCTauD2_fix ha.1 ha.2 (higmanVCTauBridge_inc_cons [γ] [u0] hαβ.symm)
      (higmanVCTauD2_inc2 (e := β) [] [] hg.symm)
  · exact (mapsCone_coneSwap_left ha.1 ha.2).append (u1 :: r)
  · exact mapsCone_coneSwap_right hpq hqp
  · exact higmanVCTauD2_fix hpq hqp (higmanVCTauBridge_inc_cons (g :: u1 :: r) [] hαβ.symm)
      (higmanVCTauD2_inc2 (e := β) (u1 :: r) [] hg)
  · exact higmanVCTauD2_fix hc.1 hc.2 (higmanVCTauBridge_inc_cons [] [γ, u0] hαβ)
      (higmanVCTauBridge_inc_cons [] [g] hαβ)
  · exact (mapsCone_coneSwap_right hc.1 hc.2).append (u1 :: r)
  · unfold higmanVCTauEqTwo_Known
    rcases r with _ | ⟨u2, r⟩
    · exact Or.inr (Or.inr (Or.inl ⟨by simp, by simp, by simp, by simp⟩))
    · unfold higmanVCTauEqTwo_Opt
      refine Or.inr (Or.inr (Or.inr ⟨?_, ?_, Or.inl (Or.inl ⟨ha.1, ha.2,
        higmanVCTauDecomp_optAS hd r hαβ hg ha.1 ha.2⟩)⟩)) <;>
        simp only [List.length_cons, List.length_nil] at hn ⊢ <;> omega
  · unfold higmanVCTauEqTwo_Known
    refine Or.inr (Or.inl ⟨?_, ?_⟩) <;>
      simp only [List.length_cons, List.length_nil] at hn ⊢ <;> omega
  · unfold higmanVCTauEqTwo_Known
    refine Or.inl ⟨?_, ?_⟩ <;> simp only [List.length_cons, List.length_nil] at hn ⊢ <;> omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauDecomp_crossNilS

end GroupApproximation.BooneHigman.Metabelian.Envelope
