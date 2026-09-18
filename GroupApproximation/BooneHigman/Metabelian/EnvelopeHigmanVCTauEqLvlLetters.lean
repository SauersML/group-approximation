import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauEqLvlSwap
import GroupApproximation.Meta.AxiomGuard

/-!
# Letter choices on three letters (lane bh-met-77z)

* `higmanVCTauEqLvl_Inc`: incomparable words.
* `higmanVCTauEqLvl_inc_append`, `higmanVCTauEqLvl_head`, `higmanVCTauEqLvl_word_cases`:
  incomparability facts for one- and two-letter words.
* `higmanVCTauEqLvl_Q`: on `d ≥ 3` letters there is a word `Q` with `|Q| ≤ 2` that is
  incomparable with `c0 :: c1 :: W` and with three words, none of them a prefix of `[c0]`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- Incomparable words. -/
def higmanVCTauEqLvl_Inc {d : ℕ} (u v : List (Fin d)) : Prop := ¬ u <+: v ∧ ¬ v <+: u

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauEqLvl_Inc

/-- Extending one of two incomparable words keeps them incomparable. -/
theorem higmanVCTauEqLvl_inc_append {d : ℕ} {a b : List (Fin d)} (v : List (Fin d))
    (hab : ¬ a <+: b) (hba : ¬ b <+: a) : ¬ a <+: b ++ v ∧ ¬ b ++ v <+: a :=
  ⟨fun h => (List.prefix_or_prefix_of_prefix h (List.prefix_append b v)).elim hab hba,
    fun h => hba ((List.prefix_append b v).trans h)⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauEqLvl_inc_append

/-- A one-letter word avoiding the first letter of a nonempty word is incomparable with it. -/
theorem higmanVCTauEqLvl_head {d : ℕ} {u : List (Fin d)} (hu : u ≠ []) :
    ∃ u0 : Fin d, (∀ e : Fin d, e ≠ u0 → ¬ [e] <+: u ∧ ¬ u <+: [e]) ∧
      ∀ e : Fin d, e ≠ u0 → ∀ v : List (Fin d), ¬ [e] <+: u ++ v ∧ ¬ u ++ v <+: [e] := by
  rcases u with _ | ⟨u0, u'⟩
  · exact absurd rfl hu
  · exact ⟨u0, fun e he => higmanVCTauBridge_inc_cons [] u' he,
      fun e he v => higmanVCTauBridge_inc_cons [] (u' ++ v) he⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauEqLvl_head

/-- A word of length `≥ 2` is not a prefix of a one-letter word. -/
theorem higmanVCTauEqLvl_not_prefix_one {d : ℕ} {u : List (Fin d)} (c0 : Fin d)
    (hu : 2 ≤ u.length) : ¬ u <+: [c0] := fun h => by
  have h1 := h.length_le
  have h2 : [c0].length = 1 := rfl
  omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauEqLvl_not_prefix_one

/-- **One- and two-letter words incomparable with `u`**, for `u` not a prefix of `[c0]`. -/
theorem higmanVCTauEqLvl_word_cases {d : ℕ} (c0 : Fin d) (u : List (Fin d))
    (hu : ¬ u <+: [c0]) : ∃ u0 u1 : Fin d,
      (∀ e : Fin d, e ≠ u0 → higmanVCTauEqLvl_Inc [e] u) ∧
      (∀ z : Fin d, (u0 = c0 → z ≠ u1) → higmanVCTauEqLvl_Inc [c0, z] u) := by
  rcases u with _ | ⟨u0, _ | ⟨u1, us⟩⟩
  · exact absurd List.nil_prefix hu
  · have hc : c0 ≠ u0 := fun h => hu (by subst h; exact List.prefix_refl _)
    exact ⟨u0, u0, fun e he => higmanVCTauBridge_inc_cons [] [] he,
      fun z _ => higmanVCTauBridge_inc_cons [z] [] hc⟩
  · refine ⟨u0, u1, fun e he => higmanVCTauBridge_inc_cons [] (u1 :: us) he, fun z hz => ?_⟩
    by_cases hc : u0 = c0
    · subst hc
      exact higmanVCTauBridge_inc_pair us (hz rfl)
    · exact higmanVCTauBridge_inc_cons [z] (u1 :: us) (Ne.symm hc)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauEqLvl_word_cases

/-- **A short word incomparable with four given words** (`d ≥ 3`). -/
theorem higmanVCTauEqLvl_Q {d : ℕ} (hd : 3 ≤ d) (c0 c1 : Fin d) (W u v w : List (Fin d))
    (hu : ¬ u <+: [c0]) (hv : ¬ v <+: [c0]) (hw : ¬ w <+: [c0]) :
    ∃ Q : List (Fin d), Q.length ≤ 2 ∧ higmanVCTauEqLvl_Inc Q (c0 :: c1 :: W) ∧
      higmanVCTauEqLvl_Inc Q u ∧ higmanVCTauEqLvl_Inc Q v ∧ higmanVCTauEqLvl_Inc Q w := by
  obtain ⟨u0, u1, hu1, hu2⟩ := higmanVCTauEqLvl_word_cases c0 u hu
  obtain ⟨v0, v1, hv1, hv2⟩ := higmanVCTauEqLvl_word_cases c0 v hv
  obtain ⟨w0, w1, hw1, hw2⟩ := higmanVCTauEqLvl_word_cases c0 w hw
  have kB : ∀ e : Fin d, e ≠ c0 → e ≠ u0 → e ≠ v0 → e ≠ w0 →
      ∃ Q : List (Fin d), Q.length ≤ 2 ∧ higmanVCTauEqLvl_Inc Q (c0 :: c1 :: W) ∧
        higmanVCTauEqLvl_Inc Q u ∧ higmanVCTauEqLvl_Inc Q v ∧ higmanVCTauEqLvl_Inc Q w :=
    fun e h0 h1 h2 h3 => ⟨[e], by simp, higmanVCTauBridge_inc_cons [] (c1 :: W) h0,
      hu1 e h1, hv1 e h2, hw1 e h3⟩
  have kA : ∀ z : Fin d, z ≠ c1 → (u0 = c0 → z ≠ u1) → (v0 = c0 → z ≠ v1) →
      (w0 = c0 → z ≠ w1) →
      ∃ Q : List (Fin d), Q.length ≤ 2 ∧ higmanVCTauEqLvl_Inc Q (c0 :: c1 :: W) ∧
        higmanVCTauEqLvl_Inc Q u ∧ higmanVCTauEqLvl_Inc Q v ∧ higmanVCTauEqLvl_Inc Q w :=
    fun z h0 h1 h2 h3 => ⟨[c0, z], by simp, higmanVCTauBridge_inc_pair W h0,
      hu2 z h1, hv2 z h2, hw2 z h3⟩
  by_cases hu0 : u0 = c0
  · by_cases hv0 : v0 = c0
    · obtain ⟨e, h0, h1⟩ := higmanVCTauBridge_avoid2 hd c0 w0
      exact kB e h0 (fun h => h0 (h.trans hu0)) (fun h => h0 (h.trans hv0)) h1
    · by_cases hw0 : w0 = c0
      · obtain ⟨e, h0, h1⟩ := higmanVCTauBridge_avoid2 hd c0 v0
        exact kB e h0 (fun h => h0 (h.trans hu0)) h1 (fun h => h0 (h.trans hw0))
      · obtain ⟨z, h0, h1⟩ := higmanVCTauBridge_avoid2 hd c1 u1
        exact kA z h0 (fun _ => h1) (fun h => absurd h hv0) (fun h => absurd h hw0)
  · by_cases hv0 : v0 = c0
    · by_cases hw0 : w0 = c0
      · obtain ⟨e, h0, h1⟩ := higmanVCTauBridge_avoid2 hd c0 u0
        exact kB e h0 h1 (fun h => h0 (h.trans hv0)) (fun h => h0 (h.trans hw0))
      · obtain ⟨z, h0, h1⟩ := higmanVCTauBridge_avoid2 hd c1 v1
        exact kA z h0 (fun h => absurd h hu0) (fun _ => h1) (fun h => absurd h hw0)
    · obtain ⟨z, h0, h1⟩ := higmanVCTauBridge_avoid2 hd c1 w1
      exact kA z h0 (fun h => absurd h hu0) (fun h => absurd h hv0) (fun _ => h1)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauEqLvl_Q

end GroupApproximation.BooneHigman.Metabelian.Envelope
