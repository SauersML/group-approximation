import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauSplitAppend
import GroupApproximation.Meta.AxiomGuard

/-!
# The descent of a pair (lane bh-met-77f)

For an incomparable pair `(v, w)` which is not short (`¬ (|v| ≤ 2 ∧ |w| ≤ 2)`), with
`P, Q, X, Y := higmanVCTau_pP, pQ, pX, pY (v, w)` (lane bh-met-77e):

* `P`, `Q` are incomparable, `|P| ≤ 2`, `|Q| ≤ 3` (`higmanVCTauSplit_pair_PQ`);
* the cone swap `(P Q)` maps the cone of `X` onto `v` and that of `Y` onto `w`
  (`higmanVCTauSplit_pair_maps`);
* `X`, `Y` are incomparable (`higmanVCTauSplit_pair_incomp`);
* `|X| ≤ |v|`, `|Y| ≤ |w|`, `|X| + |Y| < |v| + |w|` (`higmanVCTauSplit_pair_len`);
* appending a letter `a` to `v` and `w` fixes `P`, `Q` and appends `a` to `X`, `Y`
  (`higmanVCTauSplit_pair_append`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

theorem higmanVCTauSplit_pP_of_le {d : ℕ} {v w : List (Fin d)} (h : w.length ≤ v.length) :
    higmanVCTau_pP (v, w) = higmanVCTau_descP v w :=
  if_pos h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauSplit_pP_of_le

theorem higmanVCTauSplit_pQ_of_le {d : ℕ} {v w : List (Fin d)} (h : w.length ≤ v.length) :
    higmanVCTau_pQ (v, w) = v.take 3 :=
  if_pos h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauSplit_pQ_of_le

theorem higmanVCTauSplit_pX_of_le {d : ℕ} {v w : List (Fin d)} (h : w.length ≤ v.length) :
    higmanVCTau_pX (v, w) = higmanVCTau_dM v w :=
  if_pos h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauSplit_pX_of_le

theorem higmanVCTauSplit_pY_of_le {d : ℕ} {v w : List (Fin d)} (h : w.length ≤ v.length) :
    higmanVCTau_pY (v, w) = higmanVCTau_dO v w :=
  if_pos h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauSplit_pY_of_le

theorem higmanVCTauSplit_pP_of_not {d : ℕ} {v w : List (Fin d)} (h : ¬ w.length ≤ v.length) :
    higmanVCTau_pP (v, w) = higmanVCTau_descP w v :=
  if_neg h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauSplit_pP_of_not

theorem higmanVCTauSplit_pQ_of_not {d : ℕ} {v w : List (Fin d)} (h : ¬ w.length ≤ v.length) :
    higmanVCTau_pQ (v, w) = w.take 3 :=
  if_neg h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauSplit_pQ_of_not

theorem higmanVCTauSplit_pX_of_not {d : ℕ} {v w : List (Fin d)} (h : ¬ w.length ≤ v.length) :
    higmanVCTau_pX (v, w) = higmanVCTau_dO w v :=
  if_neg h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauSplit_pX_of_not

theorem higmanVCTauSplit_pY_of_not {d : ℕ} {v w : List (Fin d)} (h : ¬ w.length ≤ v.length) :
    higmanVCTau_pY (v, w) = higmanVCTau_dM w v :=
  if_neg h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauSplit_pY_of_not

/-- The conjugating pair `(P, Q)` is incomparable, `|P| ≤ 2` and `|Q| ≤ 3`. -/
theorem higmanVCTauSplit_pair_PQ {d : ℕ} (hd : 1 < d) {v w : List (Fin d)}
    (hvw : ¬ v <+: w) (hwv : ¬ w <+: v) (hs : ¬ (v.length ≤ 2 ∧ w.length ≤ 2)) :
    (¬ higmanVCTau_pP (v, w) <+: higmanVCTau_pQ (v, w) ∧
        ¬ higmanVCTau_pQ (v, w) <+: higmanVCTau_pP (v, w)) ∧
      (higmanVCTau_pP (v, w)).length ≤ 2 ∧ (higmanVCTau_pQ (v, w)).length ≤ 3 := by
  by_cases h : w.length ≤ v.length
  · have hm : 3 ≤ v.length := by omega
    have hf := higmanVCTauSplit_descP_facts hd hwv hm
    rw [higmanVCTauSplit_pP_of_le h, higmanVCTauSplit_pQ_of_le h]
    refine ⟨hf.1, hf.2.2, ?_⟩
    rw [List.length_take]
    omega
  · have hm : 3 ≤ w.length := by omega
    have hf := higmanVCTauSplit_descP_facts hd hvw hm
    rw [higmanVCTauSplit_pP_of_not h, higmanVCTauSplit_pQ_of_not h]
    refine ⟨hf.1, hf.2.2, ?_⟩
    rw [List.length_take]
    omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauSplit_pair_PQ

/-- The cone swap `(P Q)` carries the cones of the descended pair onto `v` and `w`. -/
theorem higmanVCTauSplit_pair_maps {d : ℕ} (hd : 1 < d) {v w : List (Fin d)}
    (hvw : ¬ v <+: w) (hwv : ¬ w <+: v) (hs : ¬ (v.length ≤ 2 ∧ w.length ≤ 2))
    (h1 : ¬ higmanVCTau_pP (v, w) <+: higmanVCTau_pQ (v, w))
    (h2 : ¬ higmanVCTau_pQ (v, w) <+: higmanVCTau_pP (v, w)) :
    MapsCone (coneSwap (higmanVCTau_pP (v, w)) (higmanVCTau_pQ (v, w)) h1 h2)
        (higmanVCTau_pX (v, w)) v ∧
      MapsCone (coneSwap (higmanVCTau_pP (v, w)) (higmanVCTau_pQ (v, w)) h1 h2)
        (higmanVCTau_pY (v, w)) w := by
  revert h1 h2
  by_cases h : w.length ≤ v.length
  · have hm : 3 ≤ v.length := by omega
    have hf := higmanVCTauSplit_descP_facts hd hwv hm
    rw [higmanVCTauSplit_pP_of_le h, higmanVCTauSplit_pQ_of_le h, higmanVCTauSplit_pX_of_le h,
      higmanVCTauSplit_pY_of_le h]
    intro h1 h2
    exact ⟨higmanVCTauSplit_maps_dM h1 h2,
      higmanVCTauSplit_maps_dO hwv h1 h2 hf.2.1.1 hf.2.1.2 hm⟩
  · have hm : 3 ≤ w.length := by omega
    have hf := higmanVCTauSplit_descP_facts hd hvw hm
    rw [higmanVCTauSplit_pP_of_not h, higmanVCTauSplit_pQ_of_not h,
      higmanVCTauSplit_pX_of_not h, higmanVCTauSplit_pY_of_not h]
    intro h1 h2
    exact ⟨higmanVCTauSplit_maps_dO hvw h1 h2 hf.2.1.1 hf.2.1.2 hm,
      higmanVCTauSplit_maps_dM h1 h2⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauSplit_pair_maps

/-- The descended pair is incomparable. -/
theorem higmanVCTauSplit_pair_incomp {d : ℕ} (hd : 1 < d) {v w : List (Fin d)}
    (hvw : ¬ v <+: w) (hwv : ¬ w <+: v) (hs : ¬ (v.length ≤ 2 ∧ w.length ≤ 2)) :
    ¬ higmanVCTau_pX (v, w) <+: higmanVCTau_pY (v, w) ∧
      ¬ higmanVCTau_pY (v, w) <+: higmanVCTau_pX (v, w) := by
  by_cases h : w.length ≤ v.length
  · have hm : 3 ≤ v.length := by omega
    have hf := higmanVCTauSplit_descP_facts hd hwv hm
    rw [higmanVCTauSplit_pX_of_le h, higmanVCTauSplit_pY_of_le h]
    exact higmanVCTauSplit_incomp_desc hvw hwv hf.2.1.1 hf.2.1.2 hm
  · have hm : 3 ≤ w.length := by omega
    have hf := higmanVCTauSplit_descP_facts hd hvw hm
    rw [higmanVCTauSplit_pX_of_not h, higmanVCTauSplit_pY_of_not h]
    exact (higmanVCTauSplit_incomp_desc hwv hvw hf.2.1.1 hf.2.1.2 hm).symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauSplit_pair_incomp

/-- The descended pair is shorter. -/
theorem higmanVCTauSplit_pair_len {d : ℕ} (hd : 1 < d) {v w : List (Fin d)}
    (hvw : ¬ v <+: w) (hwv : ¬ w <+: v) (hs : ¬ (v.length ≤ 2 ∧ w.length ≤ 2)) :
    (higmanVCTau_pX (v, w)).length ≤ v.length ∧ (higmanVCTau_pY (v, w)).length ≤ w.length ∧
      (higmanVCTau_pX (v, w)).length + (higmanVCTau_pY (v, w)).length <
        v.length + w.length := by
  by_cases h : w.length ≤ v.length
  · have hm : 3 ≤ v.length := by omega
    have hl := higmanVCTauSplit_len_desc hd hwv hm
    rw [higmanVCTauSplit_pX_of_le h, higmanVCTauSplit_pY_of_le h]
    omega
  · have hm : 3 ≤ w.length := by omega
    have hl := higmanVCTauSplit_len_desc hd hvw hm
    rw [higmanVCTauSplit_pX_of_not h, higmanVCTauSplit_pY_of_not h]
    omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauSplit_pair_len

/-- Appending a letter to both words fixes `P`, `Q` and appends it to `X`, `Y`. -/
theorem higmanVCTauSplit_pair_append {d : ℕ} {v w : List (Fin d)}
    (hvw : ¬ v <+: w) (hwv : ¬ w <+: v) (hs : ¬ (v.length ≤ 2 ∧ w.length ≤ 2))
    (a : Fin d) :
    higmanVCTau_pP (v ++ [a], w ++ [a]) = higmanVCTau_pP (v, w) ∧
      higmanVCTau_pQ (v ++ [a], w ++ [a]) = higmanVCTau_pQ (v, w) ∧
        higmanVCTau_pX (v ++ [a], w ++ [a]) = higmanVCTau_pX (v, w) ++ [a] ∧
          higmanVCTau_pY (v ++ [a], w ++ [a]) = higmanVCTau_pY (v, w) ++ [a] := by
  have hlv : (v ++ [a]).length = v.length + 1 := by
    rw [List.length_append, List.length_singleton]
  have hlw : (w ++ [a]).length = w.length + 1 := by
    rw [List.length_append, List.length_singleton]
  by_cases h : w.length ≤ v.length
  · have hm : 3 ≤ v.length := by omega
    have h' : (w ++ [a]).length ≤ (v ++ [a]).length := by omega
    rw [higmanVCTauSplit_pP_of_le h', higmanVCTauSplit_pP_of_le h,
      higmanVCTauSplit_pQ_of_le h', higmanVCTauSplit_pQ_of_le h,
      higmanVCTauSplit_pX_of_le h', higmanVCTauSplit_pX_of_le h,
      higmanVCTauSplit_pY_of_le h', higmanVCTauSplit_pY_of_le h]
    exact ⟨higmanVCTauSplit_descP_append hwv hm a, List.take_append_of_le_length hm,
      higmanVCTauSplit_dM_append hwv hm a, higmanVCTauSplit_dO_append hwv hm a⟩
  · have hm : 3 ≤ w.length := by omega
    have h' : ¬ (w ++ [a]).length ≤ (v ++ [a]).length := by omega
    rw [higmanVCTauSplit_pP_of_not h', higmanVCTauSplit_pP_of_not h,
      higmanVCTauSplit_pQ_of_not h', higmanVCTauSplit_pQ_of_not h,
      higmanVCTauSplit_pX_of_not h', higmanVCTauSplit_pX_of_not h,
      higmanVCTauSplit_pY_of_not h', higmanVCTauSplit_pY_of_not h]
    exact ⟨higmanVCTauSplit_descP_append hvw hm a, List.take_append_of_le_length hm,
      higmanVCTauSplit_dO_append hvw hm a, higmanVCTauSplit_dM_append hvw hm a⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauSplit_pair_append

end GroupApproximation.BooneHigman.Metabelian.Envelope
