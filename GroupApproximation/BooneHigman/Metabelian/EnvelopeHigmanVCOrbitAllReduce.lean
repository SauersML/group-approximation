import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCOrbitAllFam
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCOrbitGenWire
import GroupApproximation.Meta.AxiomGuard

/-!
# Residual `W⁗`: the gap closure off the path-atom class (lane bh-met-91x)

Notation as in `EnvelopeHigmanVCOrbitGenReduce`, with `|b| = |a| + 1`.

**Proved (`EnvelopeHigmanVCOrbitAllAtom`, `EnvelopeHigmanVCOrbitAllFam`).**  Every `h` in the
path-atom class `u · m(a p, b p y y) · (t v t⁻¹)` (`u, v ∈ U`, any word `p`, any letter `y`),
and every `h` whose twist `t⁻¹ h⁻¹ t⁻¹` lies in it, satisfies `h t ∈ S`.  This contains the
atom class of `EnvelopeHigmanVCOrbitGenAtom` for **every** letter `x` (`p = [x]`, `y = x`),
not only the head of `List.finRange d` (`higmanVCOrbitAll_famCls_of_cls`,
`higmanVCOrbitAll_cls_of_gen`).

**Residual `W⁗` = `HigmanVCOrbitAllStatement`.**  This is `HigmanVCOrbitGapStatement`
(`W''`) with the pivot closure required only for `h` that is neither mixed nor in the
path-atom class `higmanVCOrbitAll_FamCls`.  `higmanVCOrbitAll_gen_of_all : W⁗ → W'''` and
`higmanVCOrbitAll_gap_of_all : W⁗ → W''`.

LOUD, on strength: as Props `W⁗ ⇔ W''' ⇔ W''` (`higmanVCOrbitAll_all_of_gen` is the trivial
converse), and all three are Higman-strength.  So `W⁗` is NOT strictly weaker than
`HigmanVCOrbitGenStatement` in logical strength.  It is strictly smaller in PROOF CONTENT
only: the classes discharged here strictly contain `higmanVCOrbitGen_Cls`.  No class-exclusion
residual of this shape can be strictly weaker as a Prop, because the excluded classes are
proved outright.  `HigmanVCOrbitGapStatement` itself is not proved.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- The pivot closure, required only for `h` neither mixed nor in the path-atom class. -/
def higmanVCOrbitAll_Closed (d L : ℕ) (a b : List (Fin d)) : Prop :=
  ∀ C : Finset (List (Fin d)), higmanVCTreeNFWitPivot_IsAC C → (∀ c ∈ C, L ≤ c.length) →
    (∃ M : ℕ, ∀ w : List (Fin d), w.length = M → ∃ c ∈ C, c <+: w) →
      ∀ h ∈ higmanVCTreeNFWitPivot_H d C, ¬ higmanVCOrbitGap_Mix d a b h →
        ¬ higmanVCOrbitAll_FamCls d a b h →
          h * higmanVCCommon_mk d (FreeGroup.of (a, b)) ∈ higmanVCTreeNFWitPivot_S d

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitAll_Closed

/-- **Residual W⁗**: the pivot closure for `h` neither mixed nor in the path-atom class.
LOUD: `W⁗ ⇔ W''' ⇔ W''` as Props.  `W⁗` is strictly smaller in proof content only. -/
def HigmanVCOrbitAllStatement : Prop :=
  ∀ d : ℕ, 1 < d → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ∃ a b : List (Fin d), a.length = n ∧
    b.length = n + 1 ∧ ¬ a <+: b ∧ ¬ b <+: a ∧ higmanVCOrbitAll_Closed d (n + 1) a b

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.HigmanVCOrbitAllStatement

/-- **`W⁗ → W''`.** -/
theorem higmanVCOrbitAll_gap_of_all (hA : HigmanVCOrbitAllStatement) :
    HigmanVCOrbitGapStatement := by
  intro d hd N
  obtain ⟨n, hn, a, b, ha, hb, hab, hba, hcl⟩ := hA d hd N
  refine ⟨n, hn, a, b, ha, hb, hab, hba, ?_⟩
  intro C hC hL hM h hh hX
  by_cases hY : higmanVCOrbitAll_FamCls d a b h
  · exact higmanVCOrbitAll_famCls_mem_S hab hba (by omega) hY
  · exact hcl C hC hL hM h hh hX hY

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitAll_gap_of_all

/-- **`W⁗ → W'''`**: the reduction below `HigmanVCOrbitGenStatement`. -/
theorem higmanVCOrbitAll_gen_of_all (hA : HigmanVCOrbitAllStatement) :
    HigmanVCOrbitGenStatement :=
  higmanVCOrbitGen_gen_of_gap (higmanVCOrbitAll_gap_of_all hA)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitAll_gen_of_all

/-- The trivial converse `W'' → W⁗`, recorded to make the Prop-equivalence explicit. -/
theorem higmanVCOrbitAll_all_of_gap (hG : HigmanVCOrbitGapStatement) :
    HigmanVCOrbitAllStatement := by
  intro d hd N
  obtain ⟨n, hn, a, b, ha, hb, hab, hba, hcl⟩ := hG d hd N
  exact ⟨n, hn, a, b, ha, hb, hab, hba, fun C hC hL hM h hh hX _ => hcl C hC hL hM h hh hX⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitAll_all_of_gap

/-- The trivial converse `W''' → W⁗`. -/
theorem higmanVCOrbitAll_all_of_gen (hG : HigmanVCOrbitGenStatement) :
    HigmanVCOrbitAllStatement :=
  higmanVCOrbitAll_all_of_gap (higmanVCOrbitGen_gap_of_gen hG)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitAll_all_of_gen

/-- **Root wiring.**  `W⁗` and the short-relation section `τ` give the swap section. -/
theorem higmanVCOrbitAll_swapSection_of_tau (hA : HigmanVCOrbitAllStatement)
    (hB : ∀ d : ℕ, 1 < d → ∃ τ : List (Fin d) × List (Fin d) → higmanVC_Q d,
      ∀ t ∈ higmanVC_rels d (fun _ => True),
        t ∉ higmanVC_rels d (fun l => l.length ≤ 3) → higmanVC_psi d τ t = 1) :
    HigmanVSwapSectionStatement :=
  higmanVCOrbitGen_swapSection_of_tau (higmanVCOrbitAll_gen_of_all hA) hB

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitAll_swapSection_of_tau

end GroupApproximation.BooneHigman.Metabelian.Envelope
