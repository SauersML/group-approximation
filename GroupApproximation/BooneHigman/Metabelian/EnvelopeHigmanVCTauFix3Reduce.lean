import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauFix3Cases
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauFix3Mirror
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauFix3Single
import GroupApproximation.Meta.AxiomGuard

/-!
# The both-fixed family decomposes (lane bh-met-92l)

**Proved outright** (every instance, for every `1 < d`, no negated-option hypothesis used):
the both-fixed family `higmanVCTauFix3_BothFixed p q x y` (`|p| = |q| = 3`, both `x` and `y`
incomparable with `p` and with `q`, so `x' = x`, `y' = y`) has a form `sas` decomposition
(`higmanVCTauFix3_bothFixed_decomp`), by the uniform rule `higmanVCTauFix3_sas`:
* `y = [e]`: `higmanVCTauFix3_sasB`; `x = [e]`: `higmanVCTauFix3_sasBR`;
* `x = t w`, `|t| = 3`, `t <+: y`: `higmanVCTauFix3_sasC`;
* `x = t w`, `|t| = 3`, `¬ t <+: y`: `higmanVCTauFix3_sasA`;
* `|x| = 2`, `y = t v`, `|t| = 3`: `higmanVCTauFix3_sasAR`.

**Reduction.**  `higmanVCTauFix3_rest_of_fix3`: `higmanVCTauFix3_RestStatement` gives
`higmanVCTauRest_RestStatement`; also `higmanVCTauFix3_decomp_of_fix3`,
`higmanVCTauFix3_d2Residual_of_fix3`, `higmanVCTauFix3_tau_of_fix3`.

**Remaining gap (LOUD).**  `higmanVCTauFix3_RestStatement` is `higmanVCTauRest_RestStatement`
with the extra hypothesis `¬ higmanVCTauFix3_BothFixed p q x y`.
* **FORMALLY EQUIVALENT** to `higmanVCTauRest_RestStatement` (and so to
  `higmanVCTauEqTwo_DecompStatement`), not strictly weaker in logical strength:
  `higmanVCTauFix3_fix3_of_rest` (trivial) and `higmanVCTauFix3_rest_of_fix3`.
* **Strictly fewer instances**: the residual of `higmanVCTauRest_RestStatement` has 4032
  instances at `L = 4` and 21312 at `L = 5` (`d = 2`, words of length `≤ L`, lane 92e), all
  both-fixed.  The residual of `higmanVCTauFix3_RestStatement` has **0** instances for
  `L ≤ 6` (scratch `bh-met-92l/cov.cpp`: every non-family, non-both-fixed instance has a
  flexible A or B option on one side, contradicting the hypotheses).  That vacuity (Step 1)
  is **not proved** here: it is the remaining gap.
* **Not circular.**  No ConjShort, ShortComplete, TFPShortComplete, CentralBalanced or
  AllAntichain; no witness `X = Q`, `c = id`; no Higman presentation; no `Q ≅ V_d`.

**Truth check.**  `bh-met-92l/rule.cpp` checks the explicit witnesses of the rule (the sas
components, all nine MapsCone facts, the flexible A / B witnesses of the three sub-instances,
all incomparabilities and level equalities) on every both-fixed instance, 0 failures:
`d = 2`, `L ≤ 8`: 7870752 instances (B 2976, B' 2976, C 1139040, A 6696000, A' 29760);
`d = 3`, `L ≤ 5`: 75737916 instances.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **The both-fixed family.**  `|p| = |q| = 3` and both `x`, `y` are incomparable with `p` and
with `q` (so fixed by the cone swap `(p q)`). -/
def higmanVCTauFix3_BothFixed {d : ℕ} (p q x y : List (Fin d)) : Prop :=
  p.length = 3 ∧ q.length = 3 ∧ (¬ x <+: p ∧ ¬ p <+: x) ∧ (¬ x <+: q ∧ ¬ q <+: x) ∧
    (¬ y <+: p ∧ ¬ p <+: y) ∧ (¬ y <+: q ∧ ¬ q <+: y)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauFix3_BothFixed

/-- **The uniform rule.**  A both-fixed instance, not both short, has a form `sas`
decomposition. -/
theorem higmanVCTauFix3_sas {d n : ℕ} (hd : 1 < d) {p q x y : List (Fin d)}
    (hpq : ¬ p <+: q) (hqp : ¬ q <+: p) (hF : higmanVCTauFix3_BothFixed p q x y)
    (hn : x.length + y.length = n) (hs : ¬ (x.length ≤ 3 ∧ y.length ≤ 3))
    (hxy : ¬ x <+: y) (hyx : ¬ y <+: x) :
    higmanVCTauEqTwo_Sas d n p q x y x y hpq hqp := by
  obtain ⟨hp, hq, hxp, hxq, hyp, hyq⟩ := hF
  have hx0 : x ≠ [] := by
    rintro rfl
    exact hxp.1 List.nil_prefix
  have hy0 : y ≠ [] := by
    rintro rfl
    exact hyp.1 List.nil_prefix
  by_cases hy1 : y.length = 1
  · obtain ⟨e, rfl⟩ := List.length_eq_one_iff.mp hy1
    rcases x with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, _ | ⟨w0, w'⟩⟩⟩⟩
    · exact (hx0 rfl).elim
    · exact (hs ⟨by simp, by simp⟩).elim
    · exact (hs ⟨by simp, by simp⟩).elim
    · exact (hs ⟨by simp, by simp⟩).elim
    · exact higmanVCTauFix3_sasB hd w' hpq hqp hp hq
        (fun h => hyx (List.cons_prefix_cons.mpr ⟨h, List.nil_prefix⟩)) hyp hyq hxp.2 hxq.2 hn
  by_cases hx1 : x.length = 1
  · obtain ⟨e, rfl⟩ := List.length_eq_one_iff.mp hx1
    rcases y with _ | ⟨y0, _ | ⟨y1, _ | ⟨y2, _ | ⟨w0, w'⟩⟩⟩⟩
    · exact (hy0 rfl).elim
    · exact (hs ⟨by simp, by simp⟩).elim
    · exact (hs ⟨by simp, by simp⟩).elim
    · exact (hs ⟨by simp, by simp⟩).elim
    · exact higmanVCTauFix3_sasBR hd w' hpq hqp hp hq
        (fun h => hxy (List.cons_prefix_cons.mpr ⟨h, List.nil_prefix⟩)) hxp hxq hyp.2 hyq.2 hn
  have hxl := List.length_pos_iff.mpr hx0
  have hyl := List.length_pos_iff.mpr hy0
  by_cases hx3 : 3 ≤ x.length
  · obtain ⟨t, w, rfl, ht⟩ := higmanVCTauFix3_split3 hx3
    by_cases hty : t <+: y
    · obtain ⟨v, rfl⟩ := hty
      exact higmanVCTauFix3_sasC hd hpq hqp hp hq ht hxp.2 hxq.2 hn
    · exact higmanVCTauFix3_sasA hd hpq hqp hp hq ht hxp.2 hxq.2 hyp hyq (by omega) hty hyx hn
  have hy3 : 3 ≤ y.length := by
    by_contra h
    exact hs ⟨by omega, by omega⟩
  obtain ⟨t, v, rfl, ht⟩ := higmanVCTauFix3_split3 hy3
  have hxt : ¬ x <+: t ∧ ¬ t <+: x := ⟨fun h => hxy (h.trans (List.prefix_append t v)),
    fun h => by
      have := h.length_le
      omega⟩
  exact higmanVCTauFix3_sasAR hd hpq hqp hp hq ht hxp hxq hyp.2 hyq.2 (by omega) hxt hn

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauFix3_sas

/-- **The both-fixed family decomposes.**  A form `sas` decomposition with known
sub-instances, for every `1 < d`. -/
theorem higmanVCTauFix3_bothFixed_decomp {d n : ℕ} (hd : 1 < d)
    {p q x y x' y' : List (Fin d)} (hpq : ¬ p <+: q) (hqp : ¬ q <+: p)
    (hF : higmanVCTauFix3_BothFixed p q x y) (hx : x.length + y.length = n)
    (hs : ¬ (x.length ≤ 3 ∧ y.length ≤ 3 ∧ x'.length ≤ 3 ∧ y'.length ≤ 3))
    (hmx : MapsCone (coneSwap p q hpq hqp) x x') (hmy : MapsCone (coneSwap p q hpq hqp) y y')
    (hxy : ¬ x <+: y) (hyx : ¬ y <+: x) :
    higmanVCTauEqTwo_Decomp d n p q x y x' y' hpq hqp := by
  haveI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have ex : x' = x := MapsCone.unique hmx (higmanVCTauD2_fix hpq hqp hF.2.2.1 hF.2.2.2.1)
  have ey : y' = y :=
    MapsCone.unique hmy (higmanVCTauD2_fix hpq hqp hF.2.2.2.2.1 hF.2.2.2.2.2)
  subst ex ey
  unfold higmanVCTauEqTwo_Decomp
  exact Or.inr (higmanVCTauFix3_sas hd hpq hqp hF hx (fun h => hs ⟨h.1, h.2, h.1, h.2⟩)
    hxy hyx)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauFix3_bothFixed_decomp
