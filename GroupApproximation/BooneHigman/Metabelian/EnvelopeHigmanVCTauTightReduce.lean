import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauTightEdge
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauCommReduce
import GroupApproximation.Meta.AxiomGuard

/-!
# The tight residual: lower-level instances by descent chains (lane bh-met-77o)

At a **lower-level** instance of `HigmanVCTauCommResidualStatement`
(`|x'| + |y'| < |x| + |y| = n`) the conjugator `s = (p, q)` is itself a node of the descent
graph of `A = (x, y)` (`EnvelopeHigmanVCTauTightEdge`), and the goal says that this node is
good.  The canonical descent pair `t` of `A` and its reverse are good (definition of `τ`),
and goodness spreads along square edges using only instances below level `n`.
`higmanVCTauTight_Chain` asks for a path `root — bridge — s` of at most two links;
`higmanVCTauTight_chain_case` proves the instance.

`HigmanVCTauTightStatement` is `HigmanVCTauCommResidualStatement` with the extra hypothesis
that a lower-level instance has no such chain.

**Strength (loud): LOGICALLY EQUIVALENT, strictly smaller in proof content.**  The tight
statement is a special case of the comm residual (`higmanVCTauTight_tight_of_commResidual`)
and implies it (`higmanVCTauTight_commResidual_of_tight`).  Scratch check
(`SP/bh-met-77o/fastR.py`, `tight.py`): every descent of every long pair has a chain of at most
two links (`d = 2`, words `≤ 6`; `d = 3`, words `≤ 5`; `d = 4`, words `≤ 4`), so every
lower-level instance of the comm residual (`d = 2`, words `≤ 5`: 10304; `d = 3`, words `≤ 4`:
41796) is removed; at `d = 3`, words `≤ 4` the tight statement has no instances left at all, and
at `d = 2`, words `≤ 5` only the 28992 equal-level ones remain.  The lower-level hypothesis is
conjecturally vacuous (not proved here: that needs a bridge for every descent, all `d`).

**Truth.**  Implied by the comm residual (a special case of it).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- A descent chain for `s = (p, q)` at `(x, y)`: `(x, y)` is long, and a root (the canonical
descent pair or its reverse) is linked to a bridge node, which is linked to `(p, q)`. -/
def higmanVCTauTight_Chain (d : ℕ) (p q x y x' y' : List (Fin d)) : Prop :=
  ¬ (x.length ≤ 3 ∧ y.length ≤ 3) ∧
    ∃ P0 Q0 X0 Y0 P1 Q1 X1 Y1 : List (Fin d),
      ((P0 = higmanVCTau_pP (x, y) ∧ Q0 = higmanVCTau_pQ (x, y)) ∨
        (P0 = higmanVCTau_pQ (x, y) ∧ Q0 = higmanVCTau_pP (x, y))) ∧
      higmanVCTauTight_Node d x y P0 Q0 X0 Y0 ∧ higmanVCTauTight_Node d x y P1 Q1 X1 Y1 ∧
      higmanVCTauTight_Link d (x.length + y.length) P0 Q0 X0 Y0 P1 Q1 X1 Y1 ∧
      higmanVCTauTight_Link d (x.length + y.length) P1 Q1 X1 Y1 p q x' y'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauTight_Chain

/-- **Chain case.**  A lower-level instance with a descent chain, from instances below `n`. -/
theorem higmanVCTauTight_chain_case {d : ℕ} (hd : 1 < d) {n : ℕ}
    (hB : higmanVCTauShort_Below d n) {p q x y x' y' : List (Fin d)}
    (hA : x.length + y.length = n) (hxy : ¬ x <+: y) (hyx : ¬ y <+: x)
    (hs : higmanVCTauTight_Node d x y p q x' y') (hC : higmanVCTauTight_Chain d p q x y x' y') :
    higmanVCTauShort_conjEq d p q x y x' y' := by
  obtain ⟨hlong, P0, Q0, X0, Y0, P1, Q1, X1, Y1, hroot, hN0, hN1, hL0, hL1⟩ := hC
  subst hA
  have g0 := higmanVCTauTight_root_good hd hlong hxy hyx hroot hN0
  have g1 := higmanVCTauTight_link_good hd hB rfl hxy hyx hN0 hN1 hL0 g0
  exact higmanVCTauTight_link_good hd hB rfl hxy hyx hN1 hs hL1 g1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauTight_chain_case

/-- **Remaining gap (tight residual).**  `HigmanVCTauCommResidualStatement` restricted to
instances that are equal-level, or lower-level without a descent chain.
**EQUIVALENT** to the comm residual (`higmanVCTauTight_iff`), smaller in proof content. -/
def HigmanVCTauTightStatement : Prop :=
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
      MapsCone (coneSwap p q hpq hqp) x x' → MapsCone (coneSwap p q hpq hqp) y y' →
      ¬ x <+: y → ¬ y <+: x → ¬ x' <+: y' → ¬ y' <+: x' →
      higmanVCTauShort_conjEq d p q x y x' y'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.HigmanVCTauTightStatement

/-- **Reduction.**  The tight residual gives the comm residual of lane bh-met-77m. -/
theorem higmanVCTauTight_commResidual_of_tight (h : HigmanVCTauTightStatement) :
    HigmanVCTauCommResidualStatement := by
  intro d hd n hB p q x y x' y' hpq hqp hp hq hA hBn hSh hs hOA hE hR hF hmx hmy hxy hyx
    hxy' hyx'
  by_cases hC : x'.length + y'.length < n ∧ higmanVCTauTight_Chain d p q x y x' y'
  · obtain ⟨hlt, hch⟩ := hC
    have hN : higmanVCTauTight_Node d x y p q x' y' := by
      unfold higmanVCTauTight_Node higmanVCTauTight_Step
      exact ⟨⟨hpq, hqp, hp, hq, hmx, hmy⟩, by omega⟩
    exact higmanVCTauTight_chain_case hd hB hA hxy hyx hN hch
  · exact h d hd n hB p q x y x' y' hpq hqp hp hq hA hBn hSh hs hOA hE hR hF
      (fun hlt hch => hC ⟨hlt, hch⟩) hmx hmy hxy hyx hxy' hyx'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauTight_commResidual_of_tight

/-- The tight residual is a special case of the comm residual. -/
theorem higmanVCTauTight_tight_of_commResidual (h : HigmanVCTauCommResidualStatement) :
    HigmanVCTauTightStatement := by
  intro d hd n hB p q x y x' y' hpq hqp hp hq hA hBn hSh hs hOA hE hR hF _ hmx hmy hxy hyx
    hxy' hyx'
  exact h d hd n hB p q x y x' y' hpq hqp hp hq hA hBn hSh hs hOA hE hR hF hmx hmy hxy hyx
    hxy' hyx'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauTight_tight_of_commResidual

/-- **Strength (loud): EQUIVALENT** to the comm residual (smaller in proof content only). -/
theorem higmanVCTauTight_iff : HigmanVCTauTightStatement ↔ HigmanVCTauCommResidualStatement :=
  ⟨higmanVCTauTight_commResidual_of_tight, higmanVCTauTight_tight_of_commResidual⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauTight_iff

/-- **Wire.**  The `τ` half (`HigmanVCTauStatement`) from the tight residual alone. -/
theorem higmanVCTauTight_tau_of_tight (h : HigmanVCTauTightStatement) : HigmanVCTauStatement :=
  higmanVCTauComm_tau_of_residual (higmanVCTauTight_commResidual_of_tight h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauTight_tau_of_tight

end GroupApproximation.BooneHigman.Metabelian.Envelope
