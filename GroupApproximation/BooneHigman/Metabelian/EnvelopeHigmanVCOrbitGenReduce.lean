import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCOrbitGenAtom
import GroupApproximation.Meta.AxiomGuard

/-!
# Residual `W'''`: the gap closure off the atom class (lane bh-met-91l)

Notation as in `EnvelopeHigmanVCOrbitGapMix` and `EnvelopeHigmanVCOrbitGenConj`, with
`|b| = |a| + 1`, and `x = 0` the head of `List.finRange d`.

**Proved (`EnvelopeHigmanVCOrbitGenAtom`).**  Every `h` in the atom class
`u · m(a x, b x x x) · (t v t⁻¹)`, `u, v ∈ U`, and every `h` whose twist `t⁻¹ h⁻¹ t⁻¹` is in
it, satisfies `h t ∈ S`.  The class contains the gap example `swap(a0, b000)` of 77x, which
the module docstring of `EnvelopeHigmanVCOrbitGapMix` lists as not mixed.  The discharge is
the atom identity
`m(a₁, b₃) t = m(a₁, b₂)⁻¹ · (m(a₂, b₂)⁻¹ t) · m(b₁, a₂)`,
with `m(a₁, b₂)` and `m(a₂, b₂)⁻¹ t` in `H_C` for the antichain
`C = a · {x i, j} ∪ b · {x x i, x j, j}` (`j ≠ x`), and `m(b₁, a₂)` balanced.

**Residual `W'''` = `HigmanVCOrbitGenStatement`.**  This is `HigmanVCOrbitGapStatement`
(`W''`) with the pivot closure required only for `h` that is neither mixed nor in the atom
class `higmanVCOrbitGen_Cls`.  `higmanVCOrbitGen_gap_of_gen : W''' → W''`.

LOUD, on strength: as Props `W''' ⇔ W''` (`higmanVCOrbitGen_gen_of_gap` is the trivial
converse), and both are Higman-strength.  So `W'''` is NOT strictly weaker in logical
strength.  It is strictly smaller than `W''` in PROOF CONTENT only: the atom class and its
twist are discharged here, including `swap(a0, b000)`.  `HigmanVCOrbitGapStatement` itself
is not proved.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- The pivot closure, required only for `h` neither mixed nor in the atom class. -/
def higmanVCOrbitGen_Closed (d L : ℕ) (a b : List (Fin d)) : Prop :=
  ∀ C : Finset (List (Fin d)), higmanVCTreeNFWitPivot_IsAC C → (∀ c ∈ C, L ≤ c.length) →
    (∃ M : ℕ, ∀ w : List (Fin d), w.length = M → ∃ c ∈ C, c <+: w) →
      ∀ h ∈ higmanVCTreeNFWitPivot_H d C, ¬ higmanVCOrbitGap_Mix d a b h →
        ¬ higmanVCOrbitGen_Cls d a b h →
          h * higmanVCCommon_mk d (FreeGroup.of (a, b)) ∈ higmanVCTreeNFWitPivot_S d

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitGen_Closed

/-- **Residual W'''**: the pivot closure for `h` neither mixed nor in the atom class.
LOUD: `W''' ⇔ W''` as Props.  `W'''` is strictly smaller in proof content only. -/
def HigmanVCOrbitGenStatement : Prop :=
  ∀ d : ℕ, 1 < d → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ∃ a b : List (Fin d), a.length = n ∧
    b.length = n + 1 ∧ ¬ a <+: b ∧ ¬ b <+: a ∧ higmanVCOrbitGen_Closed d (n + 1) a b

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.HigmanVCOrbitGenStatement

/-- **`W''' → W''`.** -/
theorem higmanVCOrbitGen_gap_of_gen (hG : HigmanVCOrbitGenStatement) :
    HigmanVCOrbitGapStatement := by
  intro d hd N
  obtain ⟨n, hn, a, b, ha, hb, hab, hba, hcl⟩ := hG d hd N
  refine ⟨n, hn, a, b, ha, hb, hab, hba, ?_⟩
  intro C hC hL hM h hh hX
  by_cases hY : higmanVCOrbitGen_Cls d a b h
  · exact higmanVCOrbitGen_cls_mem_S hab hba (by omega) hY
  · exact hcl C hC hL hM h hh hX hY

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitGen_gap_of_gen

/-- The trivial converse `W'' → W'''`, recorded to make the Prop-equivalence explicit. -/
theorem higmanVCOrbitGen_gen_of_gap (hG : HigmanVCOrbitGapStatement) :
    HigmanVCOrbitGenStatement := by
  intro d hd N
  obtain ⟨n, hn, a, b, ha, hb, hab, hba, hcl⟩ := hG d hd N
  exact ⟨n, hn, a, b, ha, hb, hab, hba, fun C hC hL hM h hh hX _ => hcl C hC hL hM h hh hX⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitGen_gen_of_gap

end GroupApproximation.BooneHigman.Metabelian.Envelope
