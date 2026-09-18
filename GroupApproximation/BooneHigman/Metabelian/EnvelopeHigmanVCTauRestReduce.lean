import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauRestFix
import GroupApproximation.Meta.AxiomGuard

/-!
# The decomposition statement off four proved families (lane bh-met-92e)

**Proved outright** (every instance, no negated-option hypothesis used):
* the cross family `|p| = 1`, `|q| = 2` (`higmanVCTauDecomp_cross_decomp`, lane bh-met-91w);
* the mirror cross family `|p| = 2`, `|q| = 1` (`higmanVCTauRest_crossSwap_decomp`, by the
  `p ↔ q` symmetry `higmanVCTauRest_decomp_symm`);
* the one-fixed family (`higmanVCTauRest_oneFixed_decomp`): `p = [α β γ]`, `q = [α β' δ]`,
  `β ≠ β'`, one of `x, y` is `p w`, the other is `[ε]` with `ε ≠ α`;
* the mirror one-fixed family (`higmanVCTauRest_oneFixedSwap_decomp`).

**Reduction.**  `higmanVCTauRest_decomp_of_rest`: `higmanVCTauRest_RestStatement` gives
`higmanVCTauEqTwo_DecompStatement`.  Also `higmanVCTauRest_d2Residual_of_rest` and
`higmanVCTauRest_tau_of_rest`.

**Remaining gap (LOUD).**  `higmanVCTauRest_RestStatement` is
`higmanVCTauEqTwo_DecompStatement` with the four extra hypotheses
`¬ Cross p q x y`, `¬ Cross q p x y`, `¬ OneFixed p q x y`, `¬ OneFixed q p x y`.
* **FORMALLY EQUIVALENT** to `higmanVCTauEqTwo_DecompStatement`, not strictly weaker in
  logical strength: `higmanVCTauRest_rest_of_decomp` (trivial) and
  `higmanVCTauRest_decomp_of_rest`.
* **Strictly smaller in proof content / strictly fewer instances**: brute force (scratch
  `bh-met-92e/rem.cpp`, `d = 2`, words of length `≤ L`): the residual of the decomposition
  statement has 5696 instances at `L = 4` and 28992 at `L = 5`; after removing the four
  families, 4032 and 21312 remain.  **Every remaining instance has `|p| = |q| = 3` and both
  `x` and `y` fixed by the cone swap** (incomparable with `p` and with `q`), so
  `x' = x`, `y' = y`.
* **Not circular.**  No ConjShort, ShortComplete, TFPShortComplete, CentralBalanced or
  AllAntichain; no witness `X = Q`, `c = id`; no Higman presentation; no `Q ≅ V_d`.

**Truth check.**  `bh-met-92e/fixrule.cpp` checks the explicit witnesses of
`EnvelopeHigmanVCTauRestFix(Words)` (sas components, the flexible A / B witnesses, all
incomparabilities and all size inequalities) on every instance of the one-fixed family,
both orientations, every `g ≠ w0`: `d = 2`, `|w| ≤ 8`: 48960 option checks, 0 bad;
`d = 3`, `|w| ≤ 4`: 466560 option checks, 0 bad.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **Remaining gap.**  `higmanVCTauEqTwo_DecompStatement` off the cross, mirror cross,
one-fixed and mirror one-fixed families.  **Formally equivalent** to the decomposition
statement (`higmanVCTauRest_rest_of_decomp`, `higmanVCTauRest_decomp_of_rest`); strictly
fewer instances (only `|p| = |q| = 3` with `x, y` both fixed survive in the brute force).
Not proved here. -/
def higmanVCTauRest_RestStatement : Prop :=
  ∀ d : ℕ, d = 2 → ∀ n : ℕ,
    ∀ (p q x y x' y' : List (Fin d)) (hpq : ¬ p <+: q) (hqp : ¬ q <+: p),
      ¬ higmanVCTauDecomp_Cross p q x y → ¬ higmanVCTauDecomp_Cross q p x y →
      ¬ higmanVCTauRest_OneFixed p q x y → ¬ higmanVCTauRest_OneFixed q p x y →
      p.length ≤ 3 → q.length ≤ 3 →
      x.length + y.length = n → x'.length + y'.length = n →
      ¬ (x.length ≤ 3 ∧ y.length ≤ 3 ∧ x'.length ≤ 3 ∧ y'.length ≤ 3) →
      ¬ higmanVCTauShort_OptionA d p q x y hpq hqp →
      ¬ higmanVCTauShort_OptionE d p q x y →
      ¬ higmanVCTauComm_OptionR d p q x y →
      ¬ higmanVCTauComm_FlexA d p q x y hpq hqp → ¬ higmanVCTauComm_FlexB d p q x y x' y' →
      ¬ higmanVCTauComm_FlexA d p q x' y' hpq hqp → ¬ higmanVCTauComm_FlexB d p q x' y' x y →
      MapsCone (coneSwap p q hpq hqp) x x' → MapsCone (coneSwap p q hpq hqp) y y' →
      ¬ x <+: y → ¬ y <+: x → ¬ x' <+: y' → ¬ y' <+: x' →
      higmanVCTauEqTwo_Decomp d n p q x y x' y' hpq hqp

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauRest_RestStatement

/-- **Reduction.**  The decomposition statement off the four families gives the full
decomposition statement. -/
theorem higmanVCTauRest_decomp_of_rest (h : higmanVCTauRest_RestStatement) :
    higmanVCTauEqTwo_DecompStatement := by
  intro d hd n p q x y x' y' hpq hqp hp hq hx hx' hs hOA hOE hOR hFA hFB hFA' hFB' hmx hmy
    hxy hyx hxy' hyx'
  by_cases hC : higmanVCTauDecomp_Cross p q x y
  · exact higmanVCTauDecomp_cross_decomp (by omega) hpq hqp hC hx hs hmx hmy
  by_cases hC' : higmanVCTauDecomp_Cross q p x y
  · exact higmanVCTauRest_crossSwap_decomp (by omega) hpq hqp hC' hx hs hmx hmy
  by_cases hF : higmanVCTauRest_OneFixed p q x y
  · exact higmanVCTauRest_oneFixed_decomp (by omega) hpq hqp hF hx hs hmx hmy
  by_cases hF' : higmanVCTauRest_OneFixed q p x y
  · exact higmanVCTauRest_oneFixedSwap_decomp (by omega) hpq hqp hF' hx hs hmx hmy
  exact h d hd n p q x y x' y' hpq hqp hC hC' hF hF' hp hq hx hx' hs hOA hOE hOR hFA hFB hFA'
    hFB' hmx hmy hxy hyx hxy' hyx'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauRest_decomp_of_rest

/-- **Converse (equivalence, loud).**  The decomposition statement gives the statement off
the four families (it only drops hypotheses). -/
theorem higmanVCTauRest_rest_of_decomp (h : higmanVCTauEqTwo_DecompStatement) :
    higmanVCTauRest_RestStatement := by
  intro d hd n p q x y x' y' hpq hqp _ _ _ _ hp hq hx hx' hs hOA hOE hOR hFA hFB hFA' hFB' hmx
    hmy hxy hyx hxy' hyx'
  exact h d hd n p q x y x' y' hpq hqp hp hq hx hx' hs hOA hOE hOR hFA hFB hFA' hFB' hmx hmy
    hxy hyx hxy' hyx'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauRest_rest_of_decomp

/-- **The `d = 2` equal-level residual** from the statement off the four families. -/
theorem higmanVCTauRest_d2Residual_of_rest (h : higmanVCTauRest_RestStatement) :
    higmanVCTauEqLvl_D2Residual :=
  higmanVCTauEqTwo_d2Residual_of_decomp (higmanVCTauRest_decomp_of_rest h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauRest_d2Residual_of_rest

/-- **`τ`** from the statement off the four families. -/
theorem higmanVCTauRest_tau_of_rest (h : higmanVCTauRest_RestStatement) :
    HigmanVCTauStatement :=
  higmanVCTauEqTwo_tau_of_decomp (higmanVCTauRest_decomp_of_rest h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauRest_tau_of_rest

end GroupApproximation.BooneHigman.Metabelian.Envelope
