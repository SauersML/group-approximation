import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauEqLvlTmpl
import GroupApproximation.Meta.AxiomGuard

/-!
# Flexible A at a word in the cone of a swapped word, equal lengths (lane bh-met-77z)

`higmanVCTauEqLvl_eqlen`: let `σ` swap `a`, `b` with `|a| = |b| ≤ 3`, let `a <+: m` with
`|m| ≥ 3`, and let `o` be a word, not a prefix of `m`, that `σ` does not lengthen.  Then the
pair `(m, o)` has the flexible-A shape (`d ≥ 3`).  The template `higmanVCTauEqLvl_tmpl` is used
at `P = m[0..3)`:
* `|a| = 1`: take `Q = [m0, z]` with `z` avoiding `m1` and the second letter of `o`, so `σ`
  carries `Q` to `b ++ [z]`;
* `|a| ≥ 2`: take `Q` from `higmanVCTauEqLvl_Q`, incomparable with `P`, `a`, `b` and `o`, so
  `σ` fixes `Q`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- The first word of an incomparable pair is nonempty. -/
theorem higmanVCTauEqLvl_len_pos {d : ℕ} {a b : List (Fin d)} (hab : ¬ a <+: b) :
    1 ≤ a.length := by
  rcases a with _ | ⟨a0, a'⟩
  · exact absurd List.nil_prefix hab
  · exact Nat.succ_le_succ (Nat.zero_le _)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauEqLvl_len_pos

/-- **Equal lengths.** -/
theorem higmanVCTauEqLvl_eqlen {d : ℕ} (hd : 3 ≤ d) {σ : Equiv.Perm (Cantor (Fin d))}
    {a b m o o' : List (Fin d)} (hs : higmanVCTauEqLvl_Sw σ a b) (ha3 : a.length ≤ 3)
    (hab : a.length = b.length) (hm : 3 ≤ m.length) (ham : a <+: m) (hom : ¬ o <+: m)
    (ho : MapsCone σ o o') (ho'l : o'.length ≤ o.length) : higmanVCTauEqLvl_FA σ m o := by
  obtain ⟨hab', hba', -, hA, -, hfix⟩ := hs
  have ha0 := higmanVCTauEqLvl_len_pos hab'
  rcases m with _ | ⟨m0, _ | ⟨m1, _ | ⟨m2, R⟩⟩⟩
  · simp at hm
  · simp at hm
  · simp at hm
  have hPm : [m0, m1, m2] <+: m0 :: m1 :: m2 :: R := ⟨R, rfl⟩
  have h1m : [m0] <+: m0 :: m1 :: m2 :: R := ⟨m1 :: m2 :: R, rfl⟩
  have hoP : ¬ o <+: [m0, m1, m2] := fun h => hom (h.trans hPm)
  have hw0 : ¬ o <+: [m0] := fun h => hom (h.trans h1m)
  rcases Nat.lt_or_ge a.length 2 with h1 | h2
  · have h1' : a.length = 1 := by omega
    have hp1 := List.prefix_take_iff.mpr ⟨ham, (by omega : a.length ≤ 1)⟩
    have hp1' : a <+: [m0] := hp1
    have ha : a = [m0] := hp1'.eq_of_length (h1'.trans rfl)
    obtain ⟨β, rfl⟩ := List.length_eq_one_iff.mp (show b.length = 1 by omega)
    subst ha
    obtain ⟨o0, o1, -, ho2⟩ := higmanVCTauEqLvl_word_cases m0 o hw0
    obtain ⟨z, hz1, hz2⟩ := higmanVCTauBridge_avoid2 hd m1 o1
    obtain ⟨hQP, hPQ⟩ := higmanVCTauBridge_inc_pair (e := m0) [m2] hz1
    obtain ⟨hQo, hoQ⟩ := ho2 z (fun _ => hz2)
    exact higmanVCTauEqLvl_tmpl (P := [m0, m1, m2]) (R := R) rfl hoP (by simp) hQP hPQ hQo
      hoQ (show MapsCone σ [m0, m1, m2] [β, m1, m2] from hA.append [m1, m2]) (by simp)
      (show MapsCone σ [m0, z] [β, z] from hA.append [z]) (by simp) ho ho'l
  · have hp3 := List.prefix_take_iff.mpr ⟨ham, ha3⟩
    have hp3' : a <+: [m0, m1, m2] := hp3
    obtain ⟨r, hr⟩ := hp3'
    have hrl := congrArg List.length hr
    simp only [List.length_append, List.length_cons, List.length_nil] at hrl
    have hv : ¬ b <+: [m0] := fun h => by
      rcases List.prefix_or_prefix_of_prefix ham (h.trans h1m) with h' | h'
      · exact hab' h'
      · exact hba' h'
    obtain ⟨Q, hQl, ⟨hQP, hPQ⟩, ⟨hQa, haQ⟩, ⟨hQb, hbQ⟩, ⟨hQo, hoQ⟩⟩ :=
      higmanVCTauEqLvl_Q hd m0 m1 [m2] a b o (higmanVCTauEqLvl_not_prefix_one m0 h2) hv hw0
    have hP' : MapsCone σ [m0, m1, m2] (b ++ r) := by
      rw [← hr]
      exact hA.append r
    exact higmanVCTauEqLvl_tmpl (P := [m0, m1, m2]) (R := R) rfl hoP hQl hQP hPQ hQo hoQ hP'
      (by simp only [List.length_append]; omega) (hfix Q hQa haQ hQb hbQ) hQl ho ho'l

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauEqLvl_eqlen

end GroupApproximation.BooneHigman.Metabelian.Envelope
