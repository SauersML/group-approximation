import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCOrbitStemSwap
import Mathlib.Tactic.Group
import GroupApproximation.Meta.AxiomGuard

/-!
# Residual `W⁶`: the gap closure off the empty-stem swap class (lane bh-met-92m)

Notation as in `EnvelopeHigmanVCOrbitLongReduce`.

**Proved.**  The empty-stem class `higmanVCOrbitStem_Cls` holds the elements
`u · m(a, b s) · (t v t⁻¹)` and `u · m(a s, b) · (t v t⁻¹)`, where `u, v ∈ U` and `s` is an
arbitrary word.  Each `h` in this class satisfies `h t ∈ S` whenever `|b| = |a| + 1`
(`higmanVCOrbitStem_cls_mem_S`, from `EnvelopeHigmanVCOrbitStemSwap`).  This closes the
single swaps that `EnvelopeHigmanVCOrbitLongReduce` left open (empty stem, `|e| ≥ 3`), and
also covers every other length.

**Residual `W⁶` = `HigmanVCOrbitStemStatement`.**  This is `HigmanVCOrbitLongStatement`
(`W⁵`), with the pivot closure also dropped on `higmanVCOrbitStem_Cls`.  We prove
`higmanVCOrbitStem_long_of_stem : W⁶ → W⁵`, `higmanVCOrbitStem_all_of_stem : W⁶ → W⁗` and
`higmanVCOrbitStem_gap_of_stem : W⁶ → W''`.

LOUD, on strength: `W⁶ ⇔ W⁵ ⇔ W⁗ ⇔ W''` as Props (`higmanVCOrbitStem_stem_of_all` is the
trivial converse), and all of them are Higman-strength.  `W⁶` is strictly smaller in PROOF
CONTENT only: every single swap `m(a e, b e')` is now discharged.  No class-exclusion
residual can be strictly weaker as a Prop, because the excluded classes are proved outright.

LOUD, the remaining gap: the general multi-letter `h ∈ H_C` (products of several letters
of a deep antichain `C`) is untouched.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- The empty-stem class: `u · σ · (t v t⁻¹)` with `u, v ∈ U` and `σ` an empty-stem swap
`m(a, b s)` or a twisted one `m(a s, b)`. -/
def higmanVCOrbitStem_Cls (d : ℕ) (a b : List (Fin d)) (h : higmanVCCommon_Q d) : Prop :=
  ∃ u ∈ higmanVCTreeNF_U d, ∃ v ∈ higmanVCTreeNF_U d, ∃ s : List (Fin d),
    h = u * higmanVCCommon_mk d (FreeGroup.of (a, b ++ s)) *
        (higmanVCCommon_mk d (FreeGroup.of (a, b)) * v *
          (higmanVCCommon_mk d (FreeGroup.of (a, b)))⁻¹) ∨
      h = u * higmanVCCommon_mk d (FreeGroup.of (a ++ s, b)) *
        (higmanVCCommon_mk d (FreeGroup.of (a, b)) * v *
          (higmanVCCommon_mk d (FreeGroup.of (a, b)))⁻¹)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitStem_Cls

/-- **Class discharge.**  Every `h` in the empty-stem class satisfies `h t ∈ S`. -/
theorem higmanVCOrbitStem_cls_mem_S {d : ℕ} {a b : List (Fin d)} (hab : ¬ a <+: b)
    (hba : ¬ b <+: a) (hlen : b.length = a.length + 1) {h : higmanVCCommon_Q d}
    (hh : higmanVCOrbitStem_Cls d a b h) :
    h * higmanVCCommon_mk d (FreeGroup.of (a, b)) ∈ higmanVCTreeNFWitPivot_S d := by
  obtain ⟨u, hu, v, hv, s, rfl | rfl⟩ := hh
  · rw [higmanVCOrbitLong_cls_eq]
    exact higmanVCTreeNFWitPivot_S_mul_U
      (higmanVCPivotAC_U_mul_S hu (higmanVCOrbitStem_swap_mem_S hab hba hlen s)) hv
  · rw [higmanVCOrbitLong_cls_eq]
    exact higmanVCTreeNFWitPivot_S_mul_U
      (higmanVCPivotAC_U_mul_S hu (higmanVCOrbitStem_swap'_mem_S hab hba hlen s)) hv

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitStem_cls_mem_S

/-- The pivot closure, required only for `h` that is not mixed, not in the path-atom class,
not in the long-swap class and not in the empty-stem class. -/
def higmanVCOrbitStem_Closed (d L : ℕ) (a b : List (Fin d)) : Prop :=
  ∀ C : Finset (List (Fin d)), higmanVCTreeNFWitPivot_IsAC C → (∀ c ∈ C, L ≤ c.length) →
    (∃ M : ℕ, ∀ w : List (Fin d), w.length = M → ∃ c ∈ C, c <+: w) →
      ∀ h ∈ higmanVCTreeNFWitPivot_H d C, ¬ higmanVCOrbitGap_Mix d a b h →
        ¬ higmanVCOrbitAll_FamCls d a b h → ¬ higmanVCOrbitLong_Cls d a b h →
          ¬ higmanVCOrbitStem_Cls d a b h →
            h * higmanVCCommon_mk d (FreeGroup.of (a, b)) ∈ higmanVCTreeNFWitPivot_S d

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitStem_Closed

/-- **Residual W⁶**: the pivot closure off the mixed, path-atom, long-swap and empty-stem
classes.  LOUD: `W⁶ ⇔ W⁵ ⇔ W⁗ ⇔ W''` as Props.  `W⁶` is strictly smaller in proof
content only. -/
def HigmanVCOrbitStemStatement : Prop :=
  ∀ d : ℕ, 1 < d → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ∃ a b : List (Fin d), a.length = n ∧
    b.length = n + 1 ∧ ¬ a <+: b ∧ ¬ b <+: a ∧ higmanVCOrbitStem_Closed d (n + 1) a b

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.HigmanVCOrbitStemStatement

/-- **`W⁶ → W⁵`.** -/
theorem higmanVCOrbitStem_long_of_stem (hS : HigmanVCOrbitStemStatement) :
    HigmanVCOrbitLongStatement := by
  intro d hd N
  obtain ⟨n, hn, a, b, ha, hb, hab, hba, hcl⟩ := hS d hd N
  refine ⟨n, hn, a, b, ha, hb, hab, hba, ?_⟩
  intro C hC hL' hM h hh hX hY hZ
  by_cases hW : higmanVCOrbitStem_Cls d a b h
  · exact higmanVCOrbitStem_cls_mem_S hab hba (by rw [ha, hb]) hW
  · exact hcl C hC hL' hM h hh hX hY hZ hW

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitStem_long_of_stem

/-- **`W⁶ → W⁗`.** -/
theorem higmanVCOrbitStem_all_of_stem (hS : HigmanVCOrbitStemStatement) :
    HigmanVCOrbitAllStatement :=
  higmanVCOrbitLong_all_of_long (higmanVCOrbitStem_long_of_stem hS)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitStem_all_of_stem

/-- **`W⁶ → W''`.** -/
theorem higmanVCOrbitStem_gap_of_stem (hS : HigmanVCOrbitStemStatement) :
    HigmanVCOrbitGapStatement :=
  higmanVCOrbitLong_gap_of_long (higmanVCOrbitStem_long_of_stem hS)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitStem_gap_of_stem

/-- The trivial converse `W⁗ → W⁶`, recorded to make the Prop-equivalence explicit. -/
theorem higmanVCOrbitStem_stem_of_all (hA : HigmanVCOrbitAllStatement) :
    HigmanVCOrbitStemStatement := by
  intro d hd N
  obtain ⟨n, hn, a, b, ha, hb, hab, hba, hcl⟩ := higmanVCOrbitLong_long_of_all hA d hd N
  exact ⟨n, hn, a, b, ha, hb, hab, hba,
    fun C hC hL hM h hh hX hY hZ _ => hcl C hC hL hM h hh hX hY hZ⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitStem_stem_of_all

end GroupApproximation.BooneHigman.Metabelian.Envelope
