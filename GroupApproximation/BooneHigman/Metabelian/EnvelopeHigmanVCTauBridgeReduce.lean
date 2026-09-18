import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauBridgeThree
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauTightReduce
import GroupApproximation.Meta.AxiomGuard

/-!
# Bridges for lower-level instances; the equal-level tight residual (lane bh-met-77q)

**Proved (symbolic, unconditional).**  On `d ≥ 3` letters every lower-level instance
`(p, q)` at a long incomparable pair `(x, y)` has a descent chain `higmanVCTauTight_Chain`
(`higmanVCTauBridge_chain`): root `(P, Q)` (the canonical descent pair), bridge `(F, Q)` for a
fresh word `F` (`higmanVCTauBridge_fresh_exists3`), link root–bridge and link bridge–`(p, q)`
by explicit square edges (`higmanVCTauBridge_chain_of_fresh`).  On any `d ≥ 2` the same holds
whenever a fresh word exists.

**Remaining gap (loud).**  `higmanVCTauBridge_Residual`: the chain for `d = 2` instances
**without** a fresh word.  It is a special case of the full chain claim `higmanVCTauBridge_All`
and, by the proved cases, **EQUIVALENT** to it (`higmanVCTauBridge_all_iff_residual`); it is
smaller in proof content only.  So `higmanVCTauTightEq_tight_of_eq` is proved only **modulo**
this residual (`higmanVCTauTightEq_tight_of_eq_of_residual`); the unconditional version is
**NOT** proved.

**Truth check (scratch, `SP/bh-met-77q`).**  Fresh counts: `d = 4`, words `≤ 4`: all
7537152 lower-level instances fresh; `d = 3`, words `≤ 5`: all 4739472 fresh; `d = 2`, words
`≤ 5`: 13312 fresh / 21856 not; words `≤ 6`: 63744 / 99040.  The chain with bridge `(F, Q)` was
checked for every fresh `F` (`d = 2`, words `≤ 6`; `d = 3`, words `≤ 5`).  Lane bh-met-77o's
check (every descent has a chain of at most two links: `d = 2`, words `≤ 6`) supports the
residual; it is not proved for longer words.

`HigmanVCTauTightEqStatement` is `HigmanVCTauTightStatement` restricted to equal-level
instances (`|x'| + |y'| = n`); it follows from the tight statement
(`higmanVCTauTightEq_eq_of_tight`) and, with the residual, implies it.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **Proved: chains on at least three letters.** -/
theorem higmanVCTauBridge_chain {d : ℕ} (hd3 : 3 ≤ d) {p q x y x' y' : List (Fin d)}
    (hlong : ¬ (x.length ≤ 3 ∧ y.length ≤ 3)) (hxy : ¬ x <+: y) (hyx : ¬ y <+: x)
    (hpq : ¬ p <+: q) (hqp : ¬ q <+: p) (hp : p.length ≤ 3) (hq : q.length ≤ 3)
    (hmx : MapsCone (coneSwap p q hpq hqp) x x') (hmy : MapsCone (coneSwap p q hpq hqp) y y')
    (hlt : x'.length + y'.length < x.length + y.length) :
    higmanVCTauTight_Chain d p q x y x' y' := by
  obtain ⟨F, hF⟩ := higmanVCTauBridge_fresh_exists3 hd3 hlong hxy hyx hpq hqp hmx hmy hlt
  exact higmanVCTauBridge_chain_of_fresh (by omega) hlong hxy hyx hpq hqp hp hq hmx hmy hlt hF

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauBridge_chain

/-- **The full chain claim:** every lower-level instance at a long incomparable pair has a
descent chain. -/
def higmanVCTauBridge_All : Prop :=
  ∀ d : ℕ, 1 < d → ∀ (p q x y x' y' : List (Fin d)) (hpq : ¬ p <+: q) (hqp : ¬ q <+: p),
    p.length ≤ 3 → q.length ≤ 3 → ¬ (x.length ≤ 3 ∧ y.length ≤ 3) → ¬ x <+: y → ¬ y <+: x →
    MapsCone (coneSwap p q hpq hqp) x x' → MapsCone (coneSwap p q hpq hqp) y y' →
    x'.length + y'.length < x.length + y.length → higmanVCTauTight_Chain d p q x y x' y'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauBridge_All

/-- **Remaining gap (bridge residual).**  The full chain claim restricted to `d = 2` and
instances without a fresh word.  **EQUIVALENT** to `higmanVCTauBridge_All`
(`higmanVCTauBridge_all_iff_residual`), smaller in proof content. -/
def higmanVCTauBridge_Residual : Prop :=
  ∀ d : ℕ, d = 2 → ∀ (p q x y x' y' : List (Fin d)) (hpq : ¬ p <+: q) (hqp : ¬ q <+: p),
    p.length ≤ 3 → q.length ≤ 3 → ¬ (x.length ≤ 3 ∧ y.length ≤ 3) → ¬ x <+: y → ¬ y <+: x →
    MapsCone (coneSwap p q hpq hqp) x x' → MapsCone (coneSwap p q hpq hqp) y y' →
    x'.length + y'.length < x.length + y.length →
    (∀ F, ¬ higmanVCTauBridge_Fresh d p q x y F) → higmanVCTauTight_Chain d p q x y x' y'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauBridge_Residual

/-- **Reduction.**  The residual gives the full chain claim. -/
theorem higmanVCTauBridge_all_of_residual (hr : higmanVCTauBridge_Residual) :
    higmanVCTauBridge_All := by
  intro d hd p q x y x' y' hpq hqp hp hq hlong hxy hyx hmx hmy hlt
  by_cases h3 : 3 ≤ d
  · exact higmanVCTauBridge_chain h3 hlong hxy hyx hpq hqp hp hq hmx hmy hlt
  · by_cases hF : ∃ F, higmanVCTauBridge_Fresh d p q x y F
    · obtain ⟨F, hF⟩ := hF
      exact higmanVCTauBridge_chain_of_fresh hd hlong hxy hyx hpq hqp hp hq hmx hmy hlt hF
    · exact hr d (by omega) p q x y x' y' hpq hqp hp hq hlong hxy hyx hmx hmy hlt
        (fun F hF' => hF ⟨F, hF'⟩)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauBridge_all_of_residual

/-- The residual is a special case of the full chain claim. -/
theorem higmanVCTauBridge_residual_of_all (ha : higmanVCTauBridge_All) :
    higmanVCTauBridge_Residual := by
  intro d hd2 p q x y x' y' hpq hqp hp hq hlong hxy hyx hmx hmy hlt _
  exact ha d (by omega) p q x y x' y' hpq hqp hp hq hlong hxy hyx hmx hmy hlt

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauBridge_residual_of_all

/-- **Strength (loud): EQUIVALENT** (smaller in proof content only). -/
theorem higmanVCTauBridge_all_iff_residual :
    higmanVCTauBridge_All ↔ higmanVCTauBridge_Residual :=
  ⟨higmanVCTauBridge_residual_of_all, higmanVCTauBridge_all_of_residual⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauBridge_all_iff_residual

/-- **The equal-level tight residual.**  `HigmanVCTauTightStatement` restricted to instances
with `|x'| + |y'| = n`. -/
def HigmanVCTauTightEqStatement : Prop :=
  ∀ d : ℕ, 1 < d → ∀ n : ℕ, higmanVCTauShort_Below d n →
    ∀ (p q x y x' y' : List (Fin d)) (hpq : ¬ p <+: q) (hqp : ¬ q <+: p),
      p.length ≤ 3 → q.length ≤ 3 →
      x.length + y.length = n → x'.length + y'.length = n →
      higmanVCTauShort_Shrink d n →
      ¬ (x.length ≤ 3 ∧ y.length ≤ 3 ∧ x'.length ≤ 3 ∧ y'.length ≤ 3) →
      ¬ higmanVCTauShort_OptionA d p q x y hpq hqp →
      ¬ higmanVCTauShort_OptionE d p q x y →
      ¬ higmanVCTauComm_OptionR d p q x y →
      ¬ higmanVCTauComm_FlexA d p q x y hpq hqp → ¬ higmanVCTauComm_FlexB d p q x y x' y' →
      ¬ higmanVCTauComm_FlexA d p q x' y' hpq hqp → ¬ higmanVCTauComm_FlexB d p q x' y' x y →
      MapsCone (coneSwap p q hpq hqp) x x' → MapsCone (coneSwap p q hpq hqp) y y' →
      ¬ x <+: y → ¬ y <+: x → ¬ x' <+: y' → ¬ y' <+: x' →
      higmanVCTauShort_conjEq d p q x y x' y'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.HigmanVCTauTightEqStatement

/-- The equal-level residual is a special case of the tight residual. -/
theorem higmanVCTauTightEq_eq_of_tight (h : HigmanVCTauTightStatement) :
    HigmanVCTauTightEqStatement := by
  intro d hd n hB p q x y x' y' hpq hqp hp hq hA hA' hSh hs hOA hE hR hFA hFB hFA' hFB'
    hmx hmy hxy hyx hxy' hyx'
  exact h d hd n hB p q x y x' y' hpq hqp hp hq hA hA'.le (fun _ => hSh) hs hOA hE hR
    (fun _ => ⟨hFA, hFB, hFA', hFB'⟩) (fun hlt _ => absurd hA' hlt.ne) hmx hmy hxy hyx
    hxy' hyx'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauTightEq_eq_of_tight

/-- **Reduction (modulo the bridge residual).**  The equal-level residual and the full chain
claim give the tight residual: a lower-level instance has a chain, contradicting the tight
hypothesis. -/
theorem higmanVCTauTightEq_tight_of_eq_of_all (h : HigmanVCTauTightEqStatement)
    (ha : higmanVCTauBridge_All) : HigmanVCTauTightStatement := by
  intro d hd n hB p q x y x' y' hpq hqp hp hq hA hBn hSh hs hOA hE hR hF hCh hmx hmy hxy hyx
    hxy' hyx'
  by_cases heq : x'.length + y'.length = n
  · obtain ⟨h1, h2, h3, h4⟩ := hF heq
    exact h d hd n hB p q x y x' y' hpq hqp hp hq hA heq (hSh heq) hs hOA hE hR h1 h2 h3 h4
      hmx hmy hxy hyx hxy' hyx'
  · have hlt : x'.length + y'.length < n := by omega
    have hlt' : x'.length + y'.length < x.length + y.length := by omega
    exact (hCh hlt (ha d hd p q x y x' y' hpq hqp hp hq
      (higmanVCTauBridge_long hd hpq hqp hmx hmy hlt' hs) hxy hyx hmx hmy hlt')).elim

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauTightEq_tight_of_eq_of_all

/-- **Reduction (modulo the `d = 2` non-fresh residual).**  `HigmanVCTauTightEqStatement →
HigmanVCTauTightStatement`, given `higmanVCTauBridge_Residual`.  The unconditional version is
**NOT** proved. -/
theorem higmanVCTauTightEq_tight_of_eq_of_residual (h : HigmanVCTauTightEqStatement)
    (hr : higmanVCTauBridge_Residual) : HigmanVCTauTightStatement :=
  higmanVCTauTightEq_tight_of_eq_of_all h (higmanVCTauBridge_all_of_residual hr)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauTightEq_tight_of_eq_of_residual

/-- **Strength (loud).**  Given the bridge residual, the equal-level residual is
**EQUIVALENT** to the tight residual (hence to the comm residual). -/
theorem higmanVCTauTightEq_iff_of_residual (hr : higmanVCTauBridge_Residual) :
    HigmanVCTauTightEqStatement ↔ HigmanVCTauTightStatement :=
  ⟨fun h => higmanVCTauTightEq_tight_of_eq_of_residual h hr, higmanVCTauTightEq_eq_of_tight⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauTightEq_iff_of_residual

/-- **Wire (modulo the bridge residual).**  The `τ` half from the equal-level residual. -/
theorem higmanVCTauTightEq_tau_of_eq_of_residual (h : HigmanVCTauTightEqStatement)
    (hr : higmanVCTauBridge_Residual) : HigmanVCTauStatement :=
  higmanVCTauTight_tau_of_tight (higmanVCTauTightEq_tight_of_eq_of_residual h hr)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauTightEq_tau_of_eq_of_residual

end GroupApproximation.BooneHigman.Metabelian.Envelope
