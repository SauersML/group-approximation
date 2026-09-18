import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauDecompWords
import GroupApproximation.Meta.AxiomGuard

/-!
# Level-`n` options for the swapped cross family (lane bh-met-91w)

The mirror images of `EnvelopeHigmanVCTauDecompWords`, with the two words of each pair read
in the other order.  Flexible A is proved with the witnesses `X ↔ Y`, `X' ↔ Y'` exchanged.
Option A uses the canonical descent of a pair whose second word is the longer one
(`higmanVCTauSplit_pP_of_not` and its siblings).

* `higmanVCTauDecomp_flexUS`: flexible A for `([β g] [α v0])` at `(β g v', β γ u0 u)`;
* `higmanVCTauDecomp_flexES`: flexible A for `([β g] [α v0])` at `(β g v1 v'', β γ)`;
* `higmanVCTauDecomp_optAS`: option A for `([α u0] [β g])` at `(β γ, α u0 u1 u2 r)`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- Flexible A for `([β g] [α v0])` at `(β g v', β γ u0 u)`. -/
theorem higmanVCTauDecomp_flexUS {d : ℕ} {α β γ g v0 w0 u0 : Fin d} (u v' : List (Fin d))
    (hαβ : α ≠ β) (hg : g ≠ γ) (hw : w0 ≠ v0) (hc1 : ¬ [β, g] <+: [α, v0])
    (hc2 : ¬ [α, v0] <+: [β, g]) :
    higmanVCTauComm_FlexA d [β, g] [α, v0] (β :: g :: v') (β :: γ :: u0 :: u) hc1 hc2 := by
  have hPQ := higmanVCTauBridge_inc_cons [γ, u0] [w0] hαβ.symm
  unfold higmanVCTauComm_FlexA
  refine ⟨[β, γ, u0], [α, w0], β :: g :: v', α :: w0 :: u, [β, γ, u0], [α, w0], α :: v0 :: v',
    α :: w0 :: u, hPQ.1, hPQ.2, by simp, by simp, ?_, ?_, ?_, ?_, ?_, by simp, by simp, ?_, ?_,
    ?_⟩
  · exact higmanVCTauD2_fix hPQ.1 hPQ.2 (higmanVCTauD2_inc2 (e := β) v' [u0] hg)
      (higmanVCTauBridge_inc_cons (g :: v') [w0] hαβ.symm)
  · exact (mapsCone_coneSwap_right hPQ.1 hPQ.2).append u
  · simp only [List.length_cons] <;> omega
  · exact higmanVCTauD2_fix hc1 hc2 (higmanVCTauD2_inc2 (e := β) [u0] [] hg.symm)
      (higmanVCTauBridge_inc_cons [γ, u0] [v0] hαβ.symm)
  · exact higmanVCTauD2_fix hc1 hc2 (higmanVCTauBridge_inc_cons [w0] [g] hαβ)
      (higmanVCTauD2_inc2 (e := α) [] [] hw)
  · exact (mapsCone_coneSwap_left hc1 hc2).append v'
  · exact higmanVCTauD2_fix hc1 hc2 (higmanVCTauBridge_inc_cons (w0 :: u) [g] hαβ)
      (higmanVCTauD2_inc2 (e := α) u [] hw)
  · simp only [List.length_cons] <;> omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauDecomp_flexUS

/-- Flexible A for `([β g] [α v0])` at `(β g v1 v'', β γ)`. -/
theorem higmanVCTauDecomp_flexES {d : ℕ} {α β γ g v0 w0 v1 : Fin d} (v'' : List (Fin d))
    (hαβ : α ≠ β) (hg : g ≠ γ) (hw : w0 ≠ v0) (hc1 : ¬ [β, g] <+: [α, v0])
    (hc2 : ¬ [α, v0] <+: [β, g]) :
    higmanVCTauComm_FlexA d [β, g] [α, v0] (β :: g :: v1 :: v'') [β, γ] hc1 hc2 := by
  have hPQ := higmanVCTauBridge_inc_cons [g, v1] [w0] hαβ.symm
  unfold higmanVCTauComm_FlexA
  refine ⟨[β, g, v1], [α, w0], α :: w0 :: v'', [β, γ], [α, v0, v1], [α, w0], α :: w0 :: v'',
    [β, γ], hPQ.1, hPQ.2, by simp, by simp, ?_, ?_, ?_, ?_, ?_, by simp, by simp, ?_, ?_, ?_⟩
  · exact (mapsCone_coneSwap_right hPQ.1 hPQ.2).append v''
  · exact higmanVCTauD2_fix hPQ.1 hPQ.2 (higmanVCTauD2_inc2 (e := β) [] [v1] hg.symm)
      (higmanVCTauBridge_inc_cons [γ] [w0] hαβ.symm)
  · simp only [List.length_cons, List.length_nil] <;> omega
  · exact (mapsCone_coneSwap_left hc1 hc2).append [v1]
  · exact higmanVCTauD2_fix hc1 hc2 (higmanVCTauBridge_inc_cons [w0] [g] hαβ)
      (higmanVCTauD2_inc2 (e := α) [] [] hw)
  · exact higmanVCTauD2_fix hc1 hc2 (higmanVCTauBridge_inc_cons (w0 :: v'') [g] hαβ)
      (higmanVCTauD2_inc2 (e := α) v'' [] hw)
  · exact higmanVCTauD2_fix hc1 hc2 (higmanVCTauD2_inc2 (e := β) [] [] hg.symm)
      (higmanVCTauBridge_inc_cons [γ] [v0] hαβ.symm)
  · simp only [List.length_cons, List.length_nil] <;> omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauDecomp_flexES

/-- Option A for `([α u0] [β g])` at `(β γ, α u0 u1 u2 r)`: the canonical descent pair is
`([α (other u0)], [α u0 u1])`, read from the longer second word. -/
theorem higmanVCTauDecomp_optAS {d : ℕ} (hd : 1 < d) {α β γ g u0 u1 u2 : Fin d}
    (r : List (Fin d)) (hαβ : α ≠ β) (hg : g ≠ γ) (ha1 : ¬ [α, u0] <+: [β, g])
    (ha2 : ¬ [β, g] <+: [α, u0]) :
    higmanVCTauShort_OptionA d [α, u0] [β, g] [β, γ] (α :: u0 :: u1 :: u2 :: r) ha1 ha2 := by
  have hw := higmanVCTauSplit_other_ne hd u0
  have hlt : ¬ (α :: u0 :: u1 :: u2 :: r).length ≤ ([β, γ] : List (Fin d)).length := by
    simp only [List.length_cons, List.length_nil] <;> omega
  have hne : ¬ ([β, γ] : List (Fin d)).head? = some α := fun h =>
    hαβ (Option.some.inj (show some β = some α from h)).symm
  have hdP : higmanVCTau_descP (α :: u0 :: u1 :: u2 :: r) [β, γ] =
      [α, higmanVCTau_other u0] :=
    (higmanVCTauSplit_descP_cons α u0 (u1 :: u2 :: r) [β, γ]).trans (if_neg hne)
  have hnt : ¬ (α :: u0 :: u1 :: u2 :: r).take 3 <+: [β, γ] := fun h =>
    hαβ (List.cons_prefix_cons.mp (show [α, u0, u1] <+: [β, γ] from h)).1
  unfold higmanVCTauShort_OptionA
  refine ⟨fun h => ?_, [α, higmanVCTau_other u0], [β, g, u1], [β, γ],
    α :: higmanVCTau_other u0 :: u2 :: r, ?_, ?_, by simp, by simp, ?_, ?_, ?_⟩
  · have h1 := h.2
    simp only [List.length_cons] at h1 <;> omega
  · rw [higmanVCTauSplit_pP_of_not hlt, hdP]
    exact higmanVCTauD2_fix ha1 ha2 (higmanVCTauD2_inc2 (e := α) [] [] hw)
      (higmanVCTauBridge_inc_cons [higmanVCTau_other u0] [g] hαβ)
  · rw [higmanVCTauSplit_pQ_of_not hlt]
    exact (mapsCone_coneSwap_left ha1 ha2).append [u1]
  · rw [higmanVCTauSplit_pX_of_not hlt, higmanVCTau_dO, if_neg hnt]
    exact higmanVCTauD2_fix ha1 ha2 (higmanVCTauBridge_inc_cons [γ] [u0] hαβ.symm)
      (higmanVCTauD2_inc2 (e := β) [] [] hg.symm)
  · rw [higmanVCTauSplit_pY_of_not hlt, higmanVCTau_dM, hdP]
    exact higmanVCTauD2_fix ha1 ha2 (higmanVCTauD2_inc2 (e := α) (u2 :: r) [] hw)
      (higmanVCTauBridge_inc_cons (higmanVCTau_other u0 :: u2 :: r) [g] hαβ)
  · simp only [List.length_cons, List.length_nil] <;> omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauDecomp_optAS

end GroupApproximation.BooneHigman.Metabelian.Envelope
