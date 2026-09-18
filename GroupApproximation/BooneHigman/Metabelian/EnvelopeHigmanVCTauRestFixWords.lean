import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauDecompWords
import GroupApproximation.Meta.AxiomGuard

/-!
# Level-`n` options for the one-fixed family (lane bh-met-92e)

The one-fixed family: `p = [α β γ]`, `q = [α β' δ]` with `β ≠ β'`, one of `x, y` is `p w`
and the other is the single letter `[ε]` with `ε ≠ α` (fixed by the cone swap `(p q)`).
Six explicit level-`n` options for the three sub-instances of the form `sas` decompositions
of `EnvelopeHigmanVCTauRestFix` (`L`: `x = p w`; `R`: `y = p w`).

* `higmanVCTauRest_fbL1`, `higmanVCTauRest_fbR1`: flexible B for `(p, [ε])` through
  `(p, [α β'])`;
* `higmanVCTauRest_faL`, `higmanVCTauRest_faR`: flexible A for `(p q)` through
  `(p, [ε g])` with `g ≠ w0`;
* `higmanVCTauRest_fbL3`, `higmanVCTauRest_fbR3`: flexible B for `(q, [ε])` through
  `([α β], q)`.

Every cone-swap fact is a prefix replacement (`mapsCone_coneSwap_left/right` and
`MapsCone.append`) or a fixed word incomparable with both swapped words
(`higmanVCTauD2_fix`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- Flexible B for `(p, [ε])` at `(p w, [ε])`, second side `(ε w, p)`. -/
theorem higmanVCTauRest_fbL1 {d : ℕ} {α β β' γ ε : Fin d} (w : List (Fin d)) (hβ : β ≠ β')
    (hε : ε ≠ α) :
    higmanVCTauComm_FlexB d [α, β, γ] [ε] (α :: β :: γ :: w) [ε] (ε :: w) [α, β, γ] := by
  have hPQ := higmanVCTauD2_inc2 (e := α) [γ] [] hβ
  unfold higmanVCTauComm_FlexB
  refine ⟨[α, β, γ], [α, β'], α :: β' :: w, [ε], [α, β'], [ε], ε :: w, [α, β'], hPQ.1, hPQ.2,
    by simp, by simp, ?_, ?_, ?_, ?_, ?_, by simp, by simp, ?_, ?_, ?_⟩
  · exact (mapsCone_coneSwap_right hPQ.1 hPQ.2).append w
  · exact higmanVCTauD2_fix hPQ.1 hPQ.2 (higmanVCTauBridge_inc_cons [] [β, γ] hε)
      (higmanVCTauBridge_inc_cons [] [β'] hε)
  · simp only [List.length_cons, List.length_nil] <;> omega
  · exact mapsCone_coneSwap_left hPQ.1 hPQ.2
  · exact higmanVCTauD2_fix hPQ.1 hPQ.2 (higmanVCTauBridge_inc_cons [] [β, γ] hε)
      (higmanVCTauBridge_inc_cons [] [β'] hε)
  · exact higmanVCTauD2_fix hPQ.1 hPQ.2 (higmanVCTauBridge_inc_cons w [β, γ] hε)
      (higmanVCTauBridge_inc_cons w [β'] hε)
  · exact mapsCone_coneSwap_left hPQ.1 hPQ.2
  · simp only [List.length_cons, List.length_nil] <;> omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauRest_fbL1

/-- Flexible B for `([ε], p)` at `([ε], p w)`, second side `(p, ε w)`. -/
theorem higmanVCTauRest_fbR1 {d : ℕ} {α β β' γ ε : Fin d} (w : List (Fin d)) (hβ : β ≠ β')
    (hε : ε ≠ α) :
    higmanVCTauComm_FlexB d [ε] [α, β, γ] [ε] (α :: β :: γ :: w) [α, β, γ] (ε :: w) := by
  have hPQ := higmanVCTauD2_inc2 (e := α) [γ] [] hβ
  unfold higmanVCTauComm_FlexB
  refine ⟨[α, β, γ], [α, β'], [ε], α :: β' :: w, [ε], [α, β'], [α, β'], ε :: w, hPQ.1, hPQ.2,
    by simp, by simp, ?_, ?_, ?_, ?_, ?_, by simp, by simp, ?_, ?_, ?_⟩
  · exact higmanVCTauD2_fix hPQ.1 hPQ.2 (higmanVCTauBridge_inc_cons [] [β, γ] hε)
      (higmanVCTauBridge_inc_cons [] [β'] hε)
  · exact (mapsCone_coneSwap_right hPQ.1 hPQ.2).append w
  · simp only [List.length_cons, List.length_nil] <;> omega
  · exact higmanVCTauD2_fix hPQ.1 hPQ.2 (higmanVCTauBridge_inc_cons [] [β, γ] hε)
      (higmanVCTauBridge_inc_cons [] [β'] hε)
  · exact mapsCone_coneSwap_left hPQ.1 hPQ.2
  · exact mapsCone_coneSwap_left hPQ.1 hPQ.2
  · exact higmanVCTauD2_fix hPQ.1 hPQ.2 (higmanVCTauBridge_inc_cons w [β, γ] hε)
      (higmanVCTauBridge_inc_cons w [β'] hε)
  · simp only [List.length_cons, List.length_nil] <;> omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauRest_fbR1

/-- Flexible A for `(p q)` at `(ε w0 w', p)`. -/
theorem higmanVCTauRest_faL {d : ℕ} {α β β' γ δ ε w0 g : Fin d} (w' : List (Fin d))
    (hε : ε ≠ α) (hg : g ≠ w0) (hpq : ¬ [α, β, γ] <+: [α, β', δ])
    (hqp : ¬ [α, β', δ] <+: [α, β, γ]) :
    higmanVCTauComm_FlexA d [α, β, γ] [α, β', δ] (ε :: w0 :: w') [α, β, γ] hpq hqp := by
  have hPQ := higmanVCTauBridge_inc_cons [β, γ] [g] hε.symm
  unfold higmanVCTauComm_FlexA
  refine ⟨[α, β, γ], [ε, g], ε :: w0 :: w', [ε, g], [α, β', δ], [ε, g], ε :: w0 :: w', [ε, g],
    hPQ.1, hPQ.2, by simp, by simp, ?_, ?_, ?_, ?_, ?_, by simp, by simp, ?_, ?_, ?_⟩
  · exact higmanVCTauD2_fix hPQ.1 hPQ.2 (higmanVCTauBridge_inc_cons (w0 :: w') [β, γ] hε)
      (higmanVCTauD2_inc2 (e := ε) w' [] hg.symm)
  · exact mapsCone_coneSwap_right hPQ.1 hPQ.2
  · simp only [List.length_cons, List.length_nil] <;> omega
  · exact mapsCone_coneSwap_left hpq hqp
  · exact higmanVCTauD2_fix hpq hqp (higmanVCTauBridge_inc_cons [g] [β, γ] hε)
      (higmanVCTauBridge_inc_cons [g] [β', δ] hε)
  · exact higmanVCTauD2_fix hpq hqp (higmanVCTauBridge_inc_cons (w0 :: w') [β, γ] hε)
      (higmanVCTauBridge_inc_cons (w0 :: w') [β', δ] hε)
  · exact higmanVCTauD2_fix hpq hqp (higmanVCTauBridge_inc_cons [g] [β, γ] hε)
      (higmanVCTauBridge_inc_cons [g] [β', δ] hε)
  · simp only [List.length_cons, List.length_nil] <;> omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauRest_faL

/-- Flexible A for `(p q)` at `(p, ε w0 w')`. -/
theorem higmanVCTauRest_faR {d : ℕ} {α β β' γ δ ε w0 g : Fin d} (w' : List (Fin d))
    (hε : ε ≠ α) (hg : g ≠ w0) (hpq : ¬ [α, β, γ] <+: [α, β', δ])
    (hqp : ¬ [α, β', δ] <+: [α, β, γ]) :
    higmanVCTauComm_FlexA d [α, β, γ] [α, β', δ] [α, β, γ] (ε :: w0 :: w') hpq hqp := by
  have hPQ := higmanVCTauBridge_inc_cons [β, γ] [g] hε.symm
  unfold higmanVCTauComm_FlexA
  refine ⟨[α, β, γ], [ε, g], [ε, g], ε :: w0 :: w', [α, β', δ], [ε, g], [ε, g], ε :: w0 :: w',
    hPQ.1, hPQ.2, by simp, by simp, ?_, ?_, ?_, ?_, ?_, by simp, by simp, ?_, ?_, ?_⟩
  · exact mapsCone_coneSwap_right hPQ.1 hPQ.2
  · exact higmanVCTauD2_fix hPQ.1 hPQ.2 (higmanVCTauBridge_inc_cons (w0 :: w') [β, γ] hε)
      (higmanVCTauD2_inc2 (e := ε) w' [] hg.symm)
  · simp only [List.length_cons, List.length_nil] <;> omega
  · exact mapsCone_coneSwap_left hpq hqp
  · exact higmanVCTauD2_fix hpq hqp (higmanVCTauBridge_inc_cons [g] [β, γ] hε)
      (higmanVCTauBridge_inc_cons [g] [β', δ] hε)
  · exact higmanVCTauD2_fix hpq hqp (higmanVCTauBridge_inc_cons [g] [β, γ] hε)
      (higmanVCTauBridge_inc_cons [g] [β', δ] hε)
  · exact higmanVCTauD2_fix hpq hqp (higmanVCTauBridge_inc_cons (w0 :: w') [β, γ] hε)
      (higmanVCTauBridge_inc_cons (w0 :: w') [β', δ] hε)
  · simp only [List.length_cons, List.length_nil] <;> omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauRest_faR

/-- Flexible B for `(q, [ε])` at `(ε w, q)`, second side `(q w, [ε])`. -/
theorem higmanVCTauRest_fbL3 {d : ℕ} {α β β' δ ε : Fin d} (w : List (Fin d)) (hβ : β ≠ β')
    (hε : ε ≠ α) :
    higmanVCTauComm_FlexB d [α, β', δ] [ε] (ε :: w) [α, β', δ] (α :: β' :: δ :: w) [ε] := by
  have hPQ := higmanVCTauD2_inc2 (e := α) [] [δ] hβ
  unfold higmanVCTauComm_FlexB
  refine ⟨[α, β], [α, β', δ], ε :: w, [α, β], [α, β], [ε], α :: β :: w, [ε], hPQ.1, hPQ.2,
    by simp, by simp, ?_, ?_, ?_, ?_, ?_, by simp, by simp, ?_, ?_, ?_⟩
  · exact higmanVCTauD2_fix hPQ.1 hPQ.2 (higmanVCTauBridge_inc_cons w [β] hε)
      (higmanVCTauBridge_inc_cons w [β', δ] hε)
  · exact mapsCone_coneSwap_left hPQ.1 hPQ.2
  · simp only [List.length_cons, List.length_nil] <;> omega
  · exact mapsCone_coneSwap_right hPQ.1 hPQ.2
  · exact higmanVCTauD2_fix hPQ.1 hPQ.2 (higmanVCTauBridge_inc_cons [] [β] hε)
      (higmanVCTauBridge_inc_cons [] [β', δ] hε)
  · exact (mapsCone_coneSwap_right hPQ.1 hPQ.2).append w
  · exact higmanVCTauD2_fix hPQ.1 hPQ.2 (higmanVCTauBridge_inc_cons [] [β] hε)
      (higmanVCTauBridge_inc_cons [] [β', δ] hε)
  · simp only [List.length_cons, List.length_nil] <;> omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauRest_fbL3

/-- Flexible B for `([ε], q)` at `(q, ε w)`, second side `([ε], q w)`. -/
theorem higmanVCTauRest_fbR3 {d : ℕ} {α β β' δ ε : Fin d} (w : List (Fin d)) (hβ : β ≠ β')
    (hε : ε ≠ α) :
    higmanVCTauComm_FlexB d [ε] [α, β', δ] [α, β', δ] (ε :: w) [ε] (α :: β' :: δ :: w) := by
  have hPQ := higmanVCTauD2_inc2 (e := α) [] [δ] hβ
  unfold higmanVCTauComm_FlexB
  refine ⟨[α, β], [α, β', δ], [α, β], ε :: w, [ε], [α, β], [ε], α :: β :: w, hPQ.1, hPQ.2,
    by simp, by simp, ?_, ?_, ?_, ?_, ?_, by simp, by simp, ?_, ?_, ?_⟩
  · exact mapsCone_coneSwap_left hPQ.1 hPQ.2
  · exact higmanVCTauD2_fix hPQ.1 hPQ.2 (higmanVCTauBridge_inc_cons w [β] hε)
      (higmanVCTauBridge_inc_cons w [β', δ] hε)
  · simp only [List.length_cons, List.length_nil] <;> omega
  · exact higmanVCTauD2_fix hPQ.1 hPQ.2 (higmanVCTauBridge_inc_cons [] [β] hε)
      (higmanVCTauBridge_inc_cons [] [β', δ] hε)
  · exact mapsCone_coneSwap_right hPQ.1 hPQ.2
  · exact higmanVCTauD2_fix hPQ.1 hPQ.2 (higmanVCTauBridge_inc_cons [] [β] hε)
      (higmanVCTauBridge_inc_cons [] [β', δ] hε)
  · exact (mapsCone_coneSwap_right hPQ.1 hPQ.2).append w
  · simp only [List.length_cons, List.length_nil] <;> omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauRest_fbR3

end GroupApproximation.BooneHigman.Metabelian.Envelope
