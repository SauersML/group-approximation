import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauEqLvlCore
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauEqLvlWire
import GroupApproximation.Meta.AxiomGuard

/-!
# The equal-level residual on `d ≥ 3` letters is vacuous (lane bh-met-77z)

**Proved.**  `higmanVCTauEqLvl_three`: on `d ≥ 3` letters, every instance of
`HigmanVCTauTightEqStatement` has flexible A or flexible B on one side, so its hypotheses
`¬ FlexA`, `¬ FlexB`, `¬ FlexA'` and `¬ FlexB'` are contradictory.  A word of length `≥ 4`
among `x, y, x', y'` is taken as `m` in `higmanVCTauEqLvl_core`.

**Remaining gap (loud).**  `higmanVCTauEqLvl_D2Residual` is the equal-level residual
restricted to `d = 2`.  It is **EQUIVALENT** to `HigmanVCTauTightEqStatement`
(`higmanVCTauEqLvl_tightEq_iff_d2`).  It is **strictly smaller in proof content only**: every
`d ≥ 3` instance is discharged here.  It is **not** strictly weaker in logical strength.
Truth: it is a special case of `HigmanVCTauTightEqStatement`, which lies downstream of
Higman's finite presentation of `V_d`.  It is **not** proved here.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **The long-word lemma** for `σ = (p q)`. -/
theorem higmanVCTauEqLvl_core {d : ℕ} (hd : 3 ≤ d) {p q m o m' o' : List (Fin d)}
    (hpq : ¬ p <+: q) (hqp : ¬ q <+: p) (hp : p.length ≤ 3) (hq : q.length ≤ 3)
    (hm : 4 ≤ m.length) (hom : ¬ o <+: m) (hmm : MapsCone (coneSwap p q hpq hqp) m m')
    (hoo : MapsCone (coneSwap p q hpq hqp) o o')
    (hlen : m'.length + o'.length = m.length + o.length) :
    higmanVCTauEqLvl_FA (coneSwap p q hpq hqp) m o ∨ higmanVCTauComm_FlexB d p q m o m' o' := by
  have hs := higmanVCTauEqLvl_sw_coneSwap hpq hqp
  rcases higmanVCTauEqLvl_cases (by omega) hs hmm with ⟨u, rfl, rfl⟩ | ⟨u, rfl, rfl⟩ |
    ⟨-, h2, -, h4, rfl⟩
  · rcases higmanVCTauEqLvl_coreM hd hs hp hq hm hom hoo hlen with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact Or.inr (higmanVCTauEqLvl_flexB_pq (higmanVCTauEqLvl_flexB_swap h))
  · rcases higmanVCTauEqLvl_coreM hd (higmanVCTauEqLvl_sw_symm hs) hq hp hm hom hoo hlen
      with h | h | h
    · exact Or.inl h
    · exact Or.inr (higmanVCTauEqLvl_flexB_pq h)
    · exact Or.inr (higmanVCTauEqLvl_flexB_swap h)
  · exact Or.inl (higmanVCTauEqLvl_coreF hd hs hp hq hm h2 h4 hom hoo (by omega))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauEqLvl_core

/-- **Vacuity on `d ≥ 3` letters**: flexible A or B holds on one side. -/
theorem higmanVCTauEqLvl_three {d : ℕ} (hd : 3 ≤ d) {p q x y x' y' : List (Fin d)}
    (hpq : ¬ p <+: q) (hqp : ¬ q <+: p) (hp : p.length ≤ 3) (hq : q.length ≤ 3)
    (hA : x.length + y.length = x'.length + y'.length)
    (hs : ¬ (x.length ≤ 3 ∧ y.length ≤ 3 ∧ x'.length ≤ 3 ∧ y'.length ≤ 3))
    (hmx : MapsCone (coneSwap p q hpq hqp) x x') (hmy : MapsCone (coneSwap p q hpq hqp) y y')
    (hxy : ¬ x <+: y) (hyx : ¬ y <+: x) (hxy' : ¬ x' <+: y') (hyx' : ¬ y' <+: x') :
    higmanVCTauComm_FlexA d p q x y hpq hqp ∨ higmanVCTauComm_FlexB d p q x y x' y' ∨
      higmanVCTauComm_FlexA d p q x' y' hpq hqp ∨ higmanVCTauComm_FlexB d p q x' y' x y := by
  have hσ := coneSwap_mul_self hpq hqp
  have hmx' := higmanVCTauConj_mapsCone_symm hmx hσ
  have hmy' := higmanVCTauConj_mapsCone_symm hmy hσ
  by_cases h1 : 4 ≤ x.length
  · rcases higmanVCTauEqLvl_core hd hpq hqp hp hq h1 hyx hmx hmy (by omega) with h | h
    · exact Or.inl (higmanVCTauEqLvl_flexA_of_FA hpq hqp h)
    · exact Or.inr (Or.inl h)
  by_cases h2 : 4 ≤ y.length
  · rcases higmanVCTauEqLvl_core hd hpq hqp hp hq h2 hxy hmy hmx (by omega) with h | h
    · exact Or.inl (higmanVCTauEqLvl_flexA_of_FA hpq hqp (higmanVCTauEqLvl_FA_swap h))
    · exact Or.inr (Or.inl (higmanVCTauEqLvl_flexB_swap h))
  by_cases h3 : 4 ≤ x'.length
  · rcases higmanVCTauEqLvl_core hd hpq hqp hp hq h3 hyx' hmx' hmy' (by omega) with h | h
    · exact Or.inr (Or.inr (Or.inl (higmanVCTauEqLvl_flexA_of_FA hpq hqp h)))
    · exact Or.inr (Or.inr (Or.inr h))
  have h4 : 4 ≤ y'.length := by
    by_contra h4
    exact hs ⟨by omega, by omega, by omega, by omega⟩
  rcases higmanVCTauEqLvl_core hd hpq hqp hp hq h4 hxy' hmy' hmx' (by omega) with h | h
  · exact Or.inr (Or.inr (Or.inl
      (higmanVCTauEqLvl_flexA_of_FA hpq hqp (higmanVCTauEqLvl_FA_swap h))))
  · exact Or.inr (Or.inr (Or.inr (higmanVCTauEqLvl_flexB_swap h)))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauEqLvl_three

/-- **The `d = 2` equal-level residual** (EQUIVALENT to `HigmanVCTauTightEqStatement`; smaller
in proof content only). -/
def higmanVCTauEqLvl_D2Residual : Prop :=
  ∀ d : ℕ, d = 2 → ∀ n : ℕ, higmanVCTauShort_Below d n →
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

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauEqLvl_D2Residual

end GroupApproximation.BooneHigman.Metabelian.Envelope
