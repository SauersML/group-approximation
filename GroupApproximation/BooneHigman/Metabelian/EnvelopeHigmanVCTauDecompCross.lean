import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauDecompWords
import GroupApproximation.Meta.AxiomGuard

/-!
# Form `sas` decompositions of the cross family (lane bh-met-91w)

The cross family: `s = ([α], [β γ])` with `α ≠ β`, `x = α u`, `y = β γ v`.  Then
`x' = β γ u` and `y' = α v`.  Let `g ≠ γ` (and `w0 ≠ v0`) be letters.

* `higmanVCTauDecomp_crossNe` (`v = v0 v'`): form `sas` with `a = ([β g], [β γ v0])`,
  `c = ([β g], [α v0])`, `A1 = (α u, β g v')`, `A2 = (β γ u, β g v')`.  The first two
  sub-instances are one level below `n`.  The third is at level `n`, by flexible A
  (`higmanVCTauDecomp_flexU`, `higmanVCTauDecomp_flexE`).  `u = v' = []` is all short.
* `higmanVCTauDecomp_crossNil` (`v = []`, `u = u0 u1 r`): form `sas` with
  `a = ([α u0], [β g])`, `c = ([β γ u0], [β g])`, `A1 = (β g u1 r, β γ)`,
  `A2 = (β g u1 r, α)`.  The first sub-instance is all short (`r = []`) or option A at level
  `n` (`higmanVCTauDecomp_optA`).  The other two are one level below `n`.

No negated-option hypothesis is used: the decompositions exist for every such instance.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **Cross family, `v = v0 v'`.**  A form `sas` decomposition. -/
theorem higmanVCTauDecomp_crossNe {d n : ℕ} (hd : 1 < d) {α β γ v0 : Fin d}
    (u v' : List (Fin d)) (hαβ : α ≠ β) (hpq : ¬ [α] <+: [β, γ]) (hqp : ¬ [β, γ] <+: [α])
    (hn : (α :: u).length + (β :: γ :: v0 :: v').length = n)
    (hns : ¬ ((α :: u).length ≤ 3 ∧ (β :: γ :: v0 :: v').length ≤ 3 ∧
      (β :: γ :: u).length ≤ 3 ∧ (α :: v0 :: v').length ≤ 3)) :
    higmanVCTauEqTwo_Sas d n [α] [β, γ] (α :: u) (β :: γ :: v0 :: v') (β :: γ :: u)
      (α :: v0 :: v') hpq hqp := by
  obtain ⟨g, hg⟩ : ∃ g : Fin d, g ≠ γ := ⟨_, higmanVCTauSplit_other_ne hd γ⟩
  obtain ⟨w0, hw⟩ : ∃ w0 : Fin d, w0 ≠ v0 := ⟨_, higmanVCTauSplit_other_ne hd v0⟩
  have ha := higmanVCTauD2_inc2 (e := β) [] [v0] hg
  have hc := higmanVCTauBridge_inc_cons [g] [v0] hαβ.symm
  have hFA : higmanVCTauComm_FlexA d [β, g] [α, v0] (β :: γ :: u) (β :: g :: v') hc.1 hc.2 := by
    rcases u with _ | ⟨u0, u⟩
    · rcases v' with _ | ⟨v1, v''⟩
      · exact (hns ⟨by simp, by simp, by simp, by simp⟩).elim
      · exact higmanVCTauDecomp_flexE v'' hαβ hg hw hc.1 hc.2
    · exact higmanVCTauDecomp_flexU u v' hαβ hg hw hc.1 hc.2
  unfold higmanVCTauEqTwo_Sas
  refine ⟨[β, g], [β, γ, v0], [β, g], [α, v0], α :: u, β :: g :: v', β :: γ :: u, β :: g :: v',
    ha.1, ha.2, hc.1, hc.2, by simp, by simp, by simp, by simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · exact higmanVCTauD2_fix hpq hqp (higmanVCTauBridge_inc_cons [g] [] hαβ.symm)
      (higmanVCTauD2_inc2 (e := β) [] [] hg)
  · exact (mapsCone_coneSwap_right hpq hqp).append [v0]
  · exact higmanVCTauD2_fix ha.1 ha.2 (higmanVCTauBridge_inc_cons u [g] hαβ)
      (higmanVCTauBridge_inc_cons u [γ, v0] hαβ)
  · exact (mapsCone_coneSwap_right ha.1 ha.2).append v'
  · exact (mapsCone_coneSwap_left hpq hqp).append u
  · exact higmanVCTauD2_fix hpq hqp (higmanVCTauBridge_inc_cons (g :: v') [] hαβ.symm)
      (higmanVCTauD2_inc2 (e := β) v' [] hg)
  · exact higmanVCTauD2_fix hc.1 hc.2 (higmanVCTauD2_inc2 (e := β) u [] hg.symm)
      (higmanVCTauBridge_inc_cons (γ :: u) [v0] hαβ.symm)
  · exact (mapsCone_coneSwap_left hc.1 hc.2).append v'
  · unfold higmanVCTauEqTwo_Known
    refine Or.inr (Or.inl ⟨?_, ?_⟩) <;> simp only [List.length_cons] at hn ⊢ <;> omega
  · unfold higmanVCTauEqTwo_Known
    refine Or.inl ⟨?_, ?_⟩ <;> simp only [List.length_cons] at hn ⊢ <;> omega
  · unfold higmanVCTauEqTwo_Known higmanVCTauEqTwo_Opt
    refine Or.inr (Or.inr (Or.inr ⟨?_, ?_, Or.inl (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨hc.1, hc.2, hFA⟩))))⟩)) <;> simp only [List.length_cons] at hn ⊢ <;> omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauDecomp_crossNe

/-- **Cross family, `v = []`, `u = u0 u1 r`.**  A form `sas` decomposition. -/
theorem higmanVCTauDecomp_crossNil {d n : ℕ} (hd : 1 < d) {α β γ u0 u1 : Fin d}
    (r : List (Fin d)) (hαβ : α ≠ β) (hpq : ¬ [α] <+: [β, γ]) (hqp : ¬ [β, γ] <+: [α])
    (hn : (α :: u0 :: u1 :: r).length + [β, γ].length = n) :
    higmanVCTauEqTwo_Sas d n [α] [β, γ] (α :: u0 :: u1 :: r) [β, γ]
      (β :: γ :: u0 :: u1 :: r) [α] hpq hqp := by
  obtain ⟨g, hg⟩ : ∃ g : Fin d, g ≠ γ := ⟨_, higmanVCTauSplit_other_ne hd γ⟩
  have ha := higmanVCTauBridge_inc_cons [u0] [g] hαβ
  have hc := higmanVCTauD2_inc2 (e := β) [u0] [] hg.symm
  unfold higmanVCTauEqTwo_Sas
  refine ⟨[α, u0], [β, g], [β, γ, u0], [β, g], β :: g :: u1 :: r, [β, γ], β :: g :: u1 :: r,
    [α], ha.1, ha.2, hc.1, hc.2, by simp, by simp, by simp, by simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · exact (mapsCone_coneSwap_left hpq hqp).append [u0]
  · exact higmanVCTauD2_fix hpq hqp (higmanVCTauBridge_inc_cons [g] [] hαβ.symm)
      (higmanVCTauD2_inc2 (e := β) [] [] hg)
  · exact (mapsCone_coneSwap_left ha.1 ha.2).append (u1 :: r)
  · exact higmanVCTauD2_fix ha.1 ha.2 (higmanVCTauBridge_inc_cons [γ] [u0] hαβ.symm)
      (higmanVCTauD2_inc2 (e := β) [] [] hg.symm)
  · exact higmanVCTauD2_fix hpq hqp (higmanVCTauBridge_inc_cons (g :: u1 :: r) [] hαβ.symm)
      (higmanVCTauD2_inc2 (e := β) (u1 :: r) [] hg)
  · exact mapsCone_coneSwap_right hpq hqp
  · exact (mapsCone_coneSwap_right hc.1 hc.2).append (u1 :: r)
  · exact higmanVCTauD2_fix hc.1 hc.2 (higmanVCTauBridge_inc_cons [] [γ, u0] hαβ)
      (higmanVCTauBridge_inc_cons [] [g] hαβ)
  · unfold higmanVCTauEqTwo_Known
    rcases r with _ | ⟨u2, r⟩
    · exact Or.inr (Or.inr (Or.inl ⟨by simp, by simp, by simp, by simp⟩))
    · unfold higmanVCTauEqTwo_Opt
      refine Or.inr (Or.inr (Or.inr ⟨?_, ?_, Or.inl (Or.inl ⟨ha.1, ha.2,
        higmanVCTauDecomp_optA hd r hαβ hg ha.1 ha.2⟩)⟩)) <;>
        simp only [List.length_cons, List.length_nil] at hn ⊢ <;> omega
  · unfold higmanVCTauEqTwo_Known
    refine Or.inr (Or.inl ⟨?_, ?_⟩) <;>
      simp only [List.length_cons, List.length_nil] at hn ⊢ <;> omega
  · unfold higmanVCTauEqTwo_Known
    refine Or.inl ⟨?_, ?_⟩ <;> simp only [List.length_cons, List.length_nil] at hn ⊢ <;> omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauDecomp_crossNil

end GroupApproximation.BooneHigman.Metabelian.Envelope
