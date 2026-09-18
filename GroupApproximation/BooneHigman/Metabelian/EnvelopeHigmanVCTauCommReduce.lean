import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauCommOptions
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauShortReduce
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauShortWire
import GroupApproximation.Meta.AxiomGuard

/-!
# The short-conjugator residual, minus Option R and the flexible squares (lane bh-met-77m)

`HigmanVCTauShortResidualStatement` (lane bh-met-77j) is reduced to
`HigmanVCTauCommResidualStatement`, which additionally assumes:

* not Option R (`higmanVCTauComm_OptionR`: `s` is the reversed canonical descent pair);
* at an equal-level instance (`|x'| + |y'| = |x| + |y| = n`, where the level-`n` hypothesis
  `higmanVCTauShort_Shrink d n` is available): neither flexible square A nor flexible square B
  applies, through any short descent pair, on either side (descending `(x, y)` or `(x', y')`).

**Strength (loud): LOGICALLY EQUIVALENT, strictly smaller in proof content.**  The new
residual is a special case of `HigmanVCTauConjShortStatement` (`higmanVCTauComm_comm_of_short`),
hence equivalent to it and to the old residual (`higmanVCTauComm_residual_iff`,
`higmanVCTauComm_residual_iff_short`).  It is not a restatement: it drops every instance
discharged by Option R and the flexible squares.  Scratch count (`bh-met-77m/cov.py`,
`cov2.py`), on the instances of the old residual:
* `d = 2`, words `≤ 5`: 209712 instances; 39296 left (18.7%), namely 28800 equal-level
  (21312 of them with `(p q)` fixing `x` and `y`), 10304 lower-level and 192 with `x`, `y`
  short;
* `d = 3`, words `≤ 4`: 4738500 instances; every equal-level one discharged, 41796
  lower-level left (0.9%).
The instances left are the tight configurations, e.g. `A = (0, 1000)`, `s = (101, 110)`:
no short descent pair of `A` or of `B` avoids the cones of `s`, and an identity among short
letters (the core of Higman's presentation theorem) is needed.

**Truth.**  Implied by the short statement, a special case of the conjugation family.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **Remaining gap.**  The oriented top-level instances of `HigmanVCTauShortResidualStatement`
that are not Option R and, at equal level, admit no flexible square on either side.
**EQUIVALENT** to `HigmanVCTauConjShortStatement` (`higmanVCTauComm_residual_iff_short`),
smaller in proof content. -/
def HigmanVCTauCommResidualStatement : Prop :=
  ∀ d : ℕ, 1 < d → ∀ n : ℕ, higmanVCTauShort_Below d n →
    ∀ (p q x y x' y' : List (Fin d)) (hpq : ¬ p <+: q) (hqp : ¬ q <+: p),
      p.length ≤ 3 → q.length ≤ 3 →
      x.length + y.length = n → x'.length + y'.length ≤ n →
      (x'.length + y'.length = n → higmanVCTauShort_Shrink d n) →
      ¬ (x.length ≤ 3 ∧ y.length ≤ 3 ∧ x'.length ≤ 3 ∧ y'.length ≤ 3) →
      ¬ higmanVCTauShort_OptionA d p q x y hpq hqp →
      ¬ higmanVCTauShort_OptionE d p q x y →
      ¬ higmanVCTauComm_OptionR d p q x y →
      (x'.length + y'.length = n →
        ¬ higmanVCTauComm_FlexA d p q x y hpq hqp ∧ ¬ higmanVCTauComm_FlexB d p q x y x' y' ∧
          ¬ higmanVCTauComm_FlexA d p q x' y' hpq hqp ∧
          ¬ higmanVCTauComm_FlexB d p q x' y' x y) →
      MapsCone (coneSwap p q hpq hqp) x x' → MapsCone (coneSwap p q hpq hqp) y y' →
      ¬ x <+: y → ¬ y <+: x → ¬ x' <+: y' → ¬ y' <+: x' →
      higmanVCTauShort_conjEq d p q x y x' y'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.HigmanVCTauCommResidualStatement

/-- **Reduction.**  The new residual gives the residual of lane bh-met-77j. -/
theorem higmanVCTauComm_residual_of_comm (h : HigmanVCTauCommResidualStatement) :
    HigmanVCTauShortResidualStatement := by
  intro d hd n hB p q x y x' y' hpq hqp hp hq hA hBn hSh hs hOA hE hmx hmy hxy hyx hxy' hyx'
  by_cases hR : higmanVCTauComm_OptionR d p q x y
  · unfold higmanVCTauComm_OptionR at hR
    obtain ⟨hlong, rfl, rfl⟩ := hR
    exact higmanVCTauComm_erev hd hlong hpq hqp hxy hyx hmx hmy
  by_cases hn : x'.length + y'.length = n
  · have hS := hSh hn
    have hss := coneSwap_mul_self hpq hqp
    have hmx' := higmanVCTauConj_mapsCone_symm hmx hss
    have hmy' := higmanVCTauConj_mapsCone_symm hmy hss
    by_cases hFA : higmanVCTauComm_FlexA d p q x y hpq hqp
    · exact higmanVCTauComm_flexA_case hd hB hS hpq hqp hp hq hA hBn hFA hmx hmy hxy hyx
        hxy' hyx'
    by_cases hFB : higmanVCTauComm_FlexB d p q x y x' y'
    · exact higmanVCTauComm_flexB_case hd hB hS hpq hqp hp hq hA hBn hFB hmx hmy hxy hyx
        hxy' hyx'
    by_cases hFA' : higmanVCTauComm_FlexA d p q x' y' hpq hqp
    · exact higmanVCTauComm_flip_eq hp hq (higmanVCTauComm_flexA_case hd hB hS hpq hqp hp hq
        hn hA.le hFA' hmx' hmy' hxy' hyx' hxy hyx)
    by_cases hFB' : higmanVCTauComm_FlexB d p q x' y' x y
    · exact higmanVCTauComm_flip_eq hp hq (higmanVCTauComm_flexB_case hd hB hS hpq hqp hp hq
        hn hA.le hFB' hmx' hmy' hxy' hyx' hxy hyx)
    exact h d hd n hB p q x y x' y' hpq hqp hp hq hA hBn hSh hs hOA hE hR
      (fun _ => ⟨hFA, hFB, hFA', hFB'⟩) hmx hmy hxy hyx hxy' hyx'
  · exact h d hd n hB p q x y x' y' hpq hqp hp hq hA hBn hSh hs hOA hE hR
      (fun h' => absurd h' hn) hmx hmy hxy hyx hxy' hyx'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauComm_residual_of_comm

/-- The new residual is a special case of the short statement. -/
theorem higmanVCTauComm_comm_of_short (h : HigmanVCTauConjShortStatement) :
    HigmanVCTauCommResidualStatement := by
  intro d hd _ _ p q x y x' y' hpq hqp hp hq _ _ _ hs _ _ _ _ hmx hmy hxy hyx hxy' hyx'
  unfold higmanVCTauShort_conjEq
  exact (higmanVCTauConj_rel_iff d (p, q) (x, y) (x', y')).mp
    (h d hd p q x y x' y' hpq hqp hp hq hs hmx hmy hxy hyx hxy' hyx')

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauComm_comm_of_short

/-- **Strength (loud): EQUIVALENT** to the short statement (smaller in proof content only). -/
theorem higmanVCTauComm_residual_iff_short :
    HigmanVCTauCommResidualStatement ↔ HigmanVCTauConjShortStatement :=
  ⟨fun h => higmanVCTauShort_short_of_residual (higmanVCTauComm_residual_of_comm h),
    higmanVCTauComm_comm_of_short⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauComm_residual_iff_short

/-- **Strength (loud): EQUIVALENT** to the residual of lane bh-met-77j. -/
theorem higmanVCTauComm_residual_iff :
    HigmanVCTauCommResidualStatement ↔ HigmanVCTauShortResidualStatement :=
  ⟨higmanVCTauComm_residual_of_comm,
    fun h => higmanVCTauComm_comm_of_short (higmanVCTauShort_short_of_residual h)⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauComm_residual_iff

/-- **Wire.**  The `τ` half (`HigmanVCTauStatement`) from the new residual alone. -/
theorem higmanVCTauComm_tau_of_residual (h : HigmanVCTauCommResidualStatement) :
    HigmanVCTauStatement :=
  higmanVCTauShortWire_tau_of_residual (higmanVCTauComm_residual_of_comm h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauComm_tau_of_residual

end GroupApproximation.BooneHigman.Metabelian.Envelope
