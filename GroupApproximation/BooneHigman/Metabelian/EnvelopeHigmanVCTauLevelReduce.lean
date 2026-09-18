import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauLevelHop
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauTightReduce
import GroupApproximation.Meta.AxiomGuard

/-!
# The equal-level part of the tight residual (lane bh-met-77r)

`HigmanVCTauTightStatement` (lane bh-met-77o) splits by the target level into
`HigmanVCTauLevelEqStatement` (`|x'| + |y'| = n`) and `HigmanVCTauLevelLtStatement`
(`|x'| + |y'| < n`, the lower-level instances owned by lane bh-met-77q);
`higmanVCTauLevel_tight_of_split` puts them back together.

`HigmanVCTauLevelResidualStatement` is the equal-level statement with three more hypotheses:
neither Hop A (from `A`, nor from `B` read backwards) nor Hop C applies
(`EnvelopeHigmanVCTauLevelHop`).  `higmanVCTauLevel_eq_of_residual` proves the equal-level
statement from it.

**Strength (loud): LOGICALLY EQUIVALENT to `HigmanVCTauLevelEqStatement`, strictly smaller in
proof content** (`higmanVCTauLevel_residual_iff`).  It is not a strictly weaker proposition.

**Truth check** (exact scratch count `SP/bh-met-77r/exact.py`, mirroring the Lean definitions;
the witness search only uses descents through prefixes of `x, y`, so the counts are upper
bounds for the Lean residual).  Equal-level tight instances and what is left:
* `d = 2`, words `≤ 4`: 5696 instances; Hop A 1344, Hop A backwards 192, Hop C 4032,
  left 128.
* `d = 2`, words `≤ 5`: 28992 instances; Hop A 6848, Hop A backwards 448, Hop C 21312,
  left 384.
* `d = 3`, words `≤ 4`: no equal-level tight instances (vacuous).
All left instances have the shape `A = (a, a' u)` with one-letter `x = a`, `|y| ∈ {4, 5}`, and
`s` swapping two depth-3 cones inside the other first-letter cone `a'`, e.g.
`(0, 1000)` with `s = (100, 110)`, target `(0, 1100)`.  They are true (a word search finds a
19-letter derivation through lower-level pairs) but need a deeper chain than one hop.

**Truth.**  Implied by the tight residual, which is equivalent to the comm residual.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **Equal-level part** of the tight residual: the extra hypothesis `|x'| + |y'| = n`. -/
def HigmanVCTauLevelEqStatement : Prop :=
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
      (x'.length + y'.length < n → ¬ higmanVCTauTight_Chain d p q x y x' y') →
      x'.length + y'.length = n →
      MapsCone (coneSwap p q hpq hqp) x x' → MapsCone (coneSwap p q hpq hqp) y y' →
      ¬ x <+: y → ¬ y <+: x → ¬ x' <+: y' → ¬ y' <+: x' →
      higmanVCTauShort_conjEq d p q x y x' y'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.HigmanVCTauLevelEqStatement

/-- **Lower-level part** of the tight residual: the extra hypothesis `|x'| + |y'| < n`. -/
def HigmanVCTauLevelLtStatement : Prop :=
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
      (x'.length + y'.length < n → ¬ higmanVCTauTight_Chain d p q x y x' y') →
      x'.length + y'.length < n →
      MapsCone (coneSwap p q hpq hqp) x x' → MapsCone (coneSwap p q hpq hqp) y y' →
      ¬ x <+: y → ¬ y <+: x → ¬ x' <+: y' → ¬ y' <+: x' →
      higmanVCTauShort_conjEq d p q x y x' y'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.HigmanVCTauLevelLtStatement

/-- **Split.**  The two level parts give the tight residual. -/
theorem higmanVCTauLevel_tight_of_split (hEq : HigmanVCTauLevelEqStatement)
    (hLt : HigmanVCTauLevelLtStatement) : HigmanVCTauTightStatement := by
  intro d hd n hB p q x y x' y' hpq hqp hp hq hA hBn hSh hs hOA hE hR hF hC hmx hmy hxy hyx
    hxy' hyx'
  by_cases hn : x'.length + y'.length = n
  · exact hEq d hd n hB p q x y x' y' hpq hqp hp hq hA hBn hSh hs hOA hE hR hF hC hn hmx hmy
      hxy hyx hxy' hyx'
  · exact hLt d hd n hB p q x y x' y' hpq hqp hp hq hA hBn hSh hs hOA hE hR hF hC (by omega)
      hmx hmy hxy hyx hxy' hyx'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauLevel_tight_of_split

/-- The equal-level part is a special case of the tight residual. -/
theorem higmanVCTauLevel_eq_of_tight (h : HigmanVCTauTightStatement) :
    HigmanVCTauLevelEqStatement := by
  intro d hd n hB p q x y x' y' hpq hqp hp hq hA hBn hSh hs hOA hE hR hF hC _ hmx hmy hxy hyx
    hxy' hyx'
  exact h d hd n hB p q x y x' y' hpq hqp hp hq hA hBn hSh hs hOA hE hR hF hC hmx hmy hxy hyx
    hxy' hyx'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauLevel_eq_of_tight

/-- The lower-level part is a special case of the tight residual. -/
theorem higmanVCTauLevel_lt_of_tight (h : HigmanVCTauTightStatement) :
    HigmanVCTauLevelLtStatement := by
  intro d hd n hB p q x y x' y' hpq hqp hp hq hA hBn hSh hs hOA hE hR hF hC _ hmx hmy hxy hyx
    hxy' hyx'
  exact h d hd n hB p q x y x' y' hpq hqp hp hq hA hBn hSh hs hOA hE hR hF hC hmx hmy hxy hyx
    hxy' hyx'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauLevel_lt_of_tight

/-- **Remaining gap (equal-level hop residual).**  `HigmanVCTauLevelEqStatement` restricted to
instances where neither Hop A (from either side) nor Hop C applies.
**EQUIVALENT** to the equal-level statement (`higmanVCTauLevel_residual_iff`). -/
def HigmanVCTauLevelResidualStatement : Prop :=
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
      (x'.length + y'.length < n → ¬ higmanVCTauTight_Chain d p q x y x' y') →
      x'.length + y'.length = n →
      ¬ higmanVCTauLevel_HopA d n p q x y x' y' hpq hqp →
      ¬ higmanVCTauLevel_HopA d n p q x' y' x y hpq hqp →
      ¬ higmanVCTauLevel_HopC d n p q x y x' y' →
      MapsCone (coneSwap p q hpq hqp) x x' → MapsCone (coneSwap p q hpq hqp) y y' →
      ¬ x <+: y → ¬ y <+: x → ¬ x' <+: y' → ¬ y' <+: x' →
      higmanVCTauShort_conjEq d p q x y x' y'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.HigmanVCTauLevelResidualStatement

/-- **Reduction.**  The hop residual gives the equal-level part of the tight residual. -/
theorem higmanVCTauLevel_eq_of_residual (h : HigmanVCTauLevelResidualStatement) :
    HigmanVCTauLevelEqStatement := by
  intro d hd n hB p q x y x' y' hpq hqp hp hq hA hBn hSh hs hOA hE hR hF hC hn hmx hmy hxy hyx
    hxy' hyx'
  have hS := hSh hn
  by_cases h1 : higmanVCTauLevel_HopA d n p q x y x' y' hpq hqp
  · exact higmanVCTauLevel_hopA_case hd hB hS hpq hqp hp hq hA h1 hmx hmy hxy hyx hxy' hyx'
  by_cases h2 : higmanVCTauLevel_HopA d n p q x' y' x y hpq hqp
  · have hss := coneSwap_mul_self hpq hqp
    exact higmanVCTauComm_flip_eq hp hq (higmanVCTauLevel_hopA_case hd hB hS hpq hqp hp hq hn
      h2 (higmanVCTauConj_mapsCone_symm hmx hss) (higmanVCTauConj_mapsCone_symm hmy hss) hxy'
      hyx' hxy hyx)
  by_cases h3 : higmanVCTauLevel_HopC d n p q x y x' y'
  · exact higmanVCTauLevel_hopC_case hd hB hS hpq hqp hp hq h3 hmx hmy hxy hyx hxy' hyx'
  exact h d hd n hB p q x y x' y' hpq hqp hp hq hA hBn hSh hs hOA hE hR hF hC hn h1 h2 h3 hmx
    hmy hxy hyx hxy' hyx'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauLevel_eq_of_residual

/-- The hop residual is a special case of the equal-level statement. -/
theorem higmanVCTauLevel_residual_of_eq (h : HigmanVCTauLevelEqStatement) :
    HigmanVCTauLevelResidualStatement := by
  intro d hd n hB p q x y x' y' hpq hqp hp hq hA hBn hSh hs hOA hE hR hF hC hn _ _ _ hmx hmy
    hxy hyx hxy' hyx'
  exact h d hd n hB p q x y x' y' hpq hqp hp hq hA hBn hSh hs hOA hE hR hF hC hn hmx hmy hxy
    hyx hxy' hyx'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauLevel_residual_of_eq

/-- **Strength (loud): EQUIVALENT** to the equal-level statement (smaller proof content only). -/
theorem higmanVCTauLevel_residual_iff :
    HigmanVCTauLevelResidualStatement ↔ HigmanVCTauLevelEqStatement :=
  ⟨higmanVCTauLevel_eq_of_residual, higmanVCTauLevel_residual_of_eq⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauLevel_residual_iff

/-- **Wire.**  The `τ` half from the hop residual and the lower-level part. -/
theorem higmanVCTauLevel_tau_of_residual (h : HigmanVCTauLevelResidualStatement)
    (hLt : HigmanVCTauLevelLtStatement) : HigmanVCTauStatement :=
  higmanVCTauTight_tau_of_tight
    (higmanVCTauLevel_tight_of_split (higmanVCTauLevel_eq_of_residual h) hLt)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauLevel_tau_of_residual

end GroupApproximation.BooneHigman.Metabelian.Envelope
