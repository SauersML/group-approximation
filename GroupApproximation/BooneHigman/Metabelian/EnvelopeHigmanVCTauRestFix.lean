import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauRestFixWords
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauRestSymm
import GroupApproximation.Meta.AxiomGuard

/-!
# Form `sas` decompositions of the one-fixed family (lane bh-met-92e)

The one-fixed family (`higmanVCTauRest_OneFixed p q x y`): `p = [α β γ]`, `q = [α β' δ]` with
`β ≠ β'`, and `(x, y) = (p w, [ε])` or `([ε], p w)` with `ε ≠ α`.  The word `[ε]` is fixed by
the cone swap `(p q)`, so `(x', y') = (q w, [ε])` or `([ε], q w)`.  Here `w = w0 w'` (the case
`w = []` is all short).

* `higmanVCTauRest_sasL` (`x = p w`): form `sas` with `a = (p, [ε])`, `c = (q, [ε])`,
  `A1 = (ε w, p)`, `A2 = (ε w, q)`;
* `higmanVCTauRest_sasR` (`y = p w`): form `sas` with `a = ([ε], p)`, `c = ([ε], q)`,
  `A1 = (p, ε w)`, `A2 = (q, ε w)`.

All three sub-instances are at level `n`.  They are known by flexible B, flexible A and
flexible B (`EnvelopeHigmanVCTauRestFixWords`).  No negated-option hypothesis is used.  The
mirror family `higmanVCTauRest_OneFixed q p x y` follows by the `p ↔ q` symmetry.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **One-fixed family, `x = p w0 w'`.**  A form `sas` decomposition. -/
theorem higmanVCTauRest_sasL {d n : ℕ} (hd : 1 < d) {α β β' γ δ ε w0 : Fin d}
    (w' : List (Fin d)) (hβ : β ≠ β') (hε : ε ≠ α) (hpq : ¬ [α, β, γ] <+: [α, β', δ])
    (hqp : ¬ [α, β', δ] <+: [α, β, γ])
    (hn : (α :: β :: γ :: w0 :: w').length + [ε].length = n) :
    higmanVCTauEqTwo_Sas d n [α, β, γ] [α, β', δ] (α :: β :: γ :: w0 :: w') [ε]
      (α :: β' :: δ :: w0 :: w') [ε] hpq hqp := by
  obtain ⟨g, hg⟩ : ∃ g : Fin d, g ≠ w0 := ⟨_, higmanVCTauSplit_other_ne hd w0⟩
  have ha := higmanVCTauBridge_inc_cons [] [β, γ] hε
  have hc := higmanVCTauBridge_inc_cons [] [β', δ] hε
  unfold higmanVCTauEqTwo_Sas
  refine ⟨[α, β, γ], [ε], [α, β', δ], [ε], ε :: w0 :: w', [α, β, γ], ε :: w0 :: w',
    [α, β', δ], ha.2, ha.1, hc.2, hc.1, by simp, by simp, by simp, by simp, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact mapsCone_coneSwap_left hpq hqp
  · exact higmanVCTauD2_fix hpq hqp ha hc
  · exact (mapsCone_coneSwap_left ha.2 ha.1).append (w0 :: w')
  · exact mapsCone_coneSwap_right ha.2 ha.1
  · exact higmanVCTauD2_fix hpq hqp (higmanVCTauBridge_inc_cons (w0 :: w') [β, γ] hε)
      (higmanVCTauBridge_inc_cons (w0 :: w') [β', δ] hε)
  · exact mapsCone_coneSwap_left hpq hqp
  · exact (mapsCone_coneSwap_right hc.2 hc.1).append (w0 :: w')
  · exact mapsCone_coneSwap_left hc.2 hc.1
  · unfold higmanVCTauEqTwo_Known higmanVCTauEqTwo_Opt
    refine Or.inr (Or.inr (Or.inr ⟨?_, ?_, Or.inl (Or.inr (Or.inr (Or.inr (Or.inr
      (higmanVCTauRest_fbL1 (w0 :: w') hβ hε)))))⟩)) <;>
      simp only [List.length_cons, List.length_nil] at hn ⊢ <;> omega
  · unfold higmanVCTauEqTwo_Known higmanVCTauEqTwo_Opt
    refine Or.inr (Or.inr (Or.inr ⟨?_, ?_, Or.inl (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨hpq, hqp, higmanVCTauRest_faL w' hε hg hpq hqp⟩))))⟩)) <;>
      simp only [List.length_cons, List.length_nil] at hn ⊢ <;> omega
  · unfold higmanVCTauEqTwo_Known higmanVCTauEqTwo_Opt
    refine Or.inr (Or.inr (Or.inr ⟨?_, ?_, Or.inl (Or.inr (Or.inr (Or.inr (Or.inr
      (higmanVCTauRest_fbL3 (w0 :: w') hβ hε)))))⟩)) <;>
      simp only [List.length_cons, List.length_nil] at hn ⊢ <;> omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauRest_sasL

/-- **One-fixed family, `y = p w0 w'`.**  A form `sas` decomposition. -/
theorem higmanVCTauRest_sasR {d n : ℕ} (hd : 1 < d) {α β β' γ δ ε w0 : Fin d}
    (w' : List (Fin d)) (hβ : β ≠ β') (hε : ε ≠ α) (hpq : ¬ [α, β, γ] <+: [α, β', δ])
    (hqp : ¬ [α, β', δ] <+: [α, β, γ])
    (hn : [ε].length + (α :: β :: γ :: w0 :: w').length = n) :
    higmanVCTauEqTwo_Sas d n [α, β, γ] [α, β', δ] [ε] (α :: β :: γ :: w0 :: w') [ε]
      (α :: β' :: δ :: w0 :: w') hpq hqp := by
  obtain ⟨g, hg⟩ : ∃ g : Fin d, g ≠ w0 := ⟨_, higmanVCTauSplit_other_ne hd w0⟩
  have ha := higmanVCTauBridge_inc_cons [] [β, γ] hε
  have hc := higmanVCTauBridge_inc_cons [] [β', δ] hε
  unfold higmanVCTauEqTwo_Sas
  refine ⟨[ε], [α, β, γ], [ε], [α, β', δ], [α, β, γ], ε :: w0 :: w', [α, β', δ],
    ε :: w0 :: w', ha.1, ha.2, hc.1, hc.2, by simp, by simp, by simp, by simp, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact higmanVCTauD2_fix hpq hqp ha hc
  · exact mapsCone_coneSwap_left hpq hqp
  · exact mapsCone_coneSwap_left ha.1 ha.2
  · exact (mapsCone_coneSwap_right ha.1 ha.2).append (w0 :: w')
  · exact mapsCone_coneSwap_left hpq hqp
  · exact higmanVCTauD2_fix hpq hqp (higmanVCTauBridge_inc_cons (w0 :: w') [β, γ] hε)
      (higmanVCTauBridge_inc_cons (w0 :: w') [β', δ] hε)
  · exact mapsCone_coneSwap_right hc.1 hc.2
  · exact (mapsCone_coneSwap_left hc.1 hc.2).append (w0 :: w')
  · unfold higmanVCTauEqTwo_Known higmanVCTauEqTwo_Opt
    refine Or.inr (Or.inr (Or.inr ⟨?_, ?_, Or.inl (Or.inr (Or.inr (Or.inr (Or.inr
      (higmanVCTauRest_fbR1 (w0 :: w') hβ hε)))))⟩)) <;>
      simp only [List.length_cons, List.length_nil] at hn ⊢ <;> omega
  · unfold higmanVCTauEqTwo_Known higmanVCTauEqTwo_Opt
    refine Or.inr (Or.inr (Or.inr ⟨?_, ?_, Or.inl (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨hpq, hqp, higmanVCTauRest_faR w' hε hg hpq hqp⟩))))⟩)) <;>
      simp only [List.length_cons, List.length_nil] at hn ⊢ <;> omega
  · unfold higmanVCTauEqTwo_Known higmanVCTauEqTwo_Opt
    refine Or.inr (Or.inr (Or.inr ⟨?_, ?_, Or.inl (Or.inr (Or.inr (Or.inr (Or.inr
      (higmanVCTauRest_fbR3 (w0 :: w') hβ hε)))))⟩)) <;>
      simp only [List.length_cons, List.length_nil] at hn ⊢ <;> omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauRest_sasR

/-- The one-fixed family: `p = [α β γ]`, `q = [α β' δ]` with `β ≠ β'`, and one of `x, y` is
`α β γ w` while the other is `[ε]` with `ε ≠ α`. -/
def higmanVCTauRest_OneFixed {d : ℕ} (p q x y : List (Fin d)) : Prop :=
  ∃ (α β β' γ δ ε : Fin d) (w : List (Fin d)), β ≠ β' ∧ ε ≠ α ∧ p = [α, β, γ] ∧
    q = [α, β', δ] ∧ ((x = α :: β :: γ :: w ∧ y = [ε]) ∨ (x = [ε] ∧ y = α :: β :: γ :: w))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauRest_OneFixed

/-- **The one-fixed family decomposes.**  A form `sas` decomposition with known
sub-instances. -/
theorem higmanVCTauRest_oneFixed_decomp {d n : ℕ} (hd : 1 < d) {p q x y x' y' : List (Fin d)}
    (hpq : ¬ p <+: q) (hqp : ¬ q <+: p) (hF : higmanVCTauRest_OneFixed p q x y)
    (hx : x.length + y.length = n)
    (hs : ¬ (x.length ≤ 3 ∧ y.length ≤ 3 ∧ x'.length ≤ 3 ∧ y'.length ≤ 3))
    (hmx : MapsCone (coneSwap p q hpq hqp) x x') (hmy : MapsCone (coneSwap p q hpq hqp) y y') :
    higmanVCTauEqTwo_Decomp d n p q x y x' y' hpq hqp := by
  haveI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr (by omega)
  unfold higmanVCTauRest_OneFixed at hF
  obtain ⟨α, β, β', γ, δ, ε, w, hβ, hε, rfl, rfl, hC⟩ := hF
  have hf := higmanVCTauD2_fix hpq hqp (higmanVCTauBridge_inc_cons [] [β, γ] hε)
    (higmanVCTauBridge_inc_cons [] [β', δ] hε)
  unfold higmanVCTauEqTwo_Decomp
  right
  rcases hC with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have ex' : x' = α :: β' :: δ :: w :=
      MapsCone.unique hmx ((mapsCone_coneSwap_left hpq hqp).append w)
    have ey' : y' = [ε] := MapsCone.unique hmy hf
    subst ex' ey'
    rcases w with _ | ⟨w0, w'⟩
    · exact (hs ⟨by simp, by simp, by simp, by simp⟩).elim
    · exact higmanVCTauRest_sasL hd w' hβ hε hpq hqp hx
  · have ex' : x' = [ε] := MapsCone.unique hmx hf
    have ey' : y' = α :: β' :: δ :: w :=
      MapsCone.unique hmy ((mapsCone_coneSwap_left hpq hqp).append w)
    subst ex' ey'
    rcases w with _ | ⟨w0, w'⟩
    · exact (hs ⟨by simp, by simp, by simp, by simp⟩).elim
    · exact higmanVCTauRest_sasR hd w' hβ hε hpq hqp hx

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauRest_oneFixed_decomp

/-- **The mirror one-fixed family decomposes** (`x` or `y` under `q`), by the `p ↔ q`
symmetry. -/
theorem higmanVCTauRest_oneFixedSwap_decomp {d n : ℕ} (hd : 1 < d)
    {p q x y x' y' : List (Fin d)} (hpq : ¬ p <+: q) (hqp : ¬ q <+: p)
    (hF : higmanVCTauRest_OneFixed q p x y) (hx : x.length + y.length = n)
    (hs : ¬ (x.length ≤ 3 ∧ y.length ≤ 3 ∧ x'.length ≤ 3 ∧ y'.length ≤ 3))
    (hmx : MapsCone (coneSwap p q hpq hqp) x x') (hmy : MapsCone (coneSwap p q hpq hqp) y y') :
    higmanVCTauEqTwo_Decomp d n p q x y x' y' hpq hqp := by
  rw [← higmanVCTauComm_coneSwap_comm hpq hqp] at hmx hmy
  exact higmanVCTauRest_decomp_symm hpq hqp
    (higmanVCTauRest_oneFixed_decomp hd hqp hpq hF hx hs hmx hmy)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauRest_oneFixedSwap_decomp

end GroupApproximation.BooneHigman.Metabelian.Envelope
