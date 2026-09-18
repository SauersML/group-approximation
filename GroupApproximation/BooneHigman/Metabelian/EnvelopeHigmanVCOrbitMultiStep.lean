import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCOrbitMultiConj
import GroupApproximation.Meta.AxiomGuard

/-!
# Residual `W⁷`: the canonical one-letter step (lane bh-met-92t)

Notation as in `EnvelopeHigmanVCOrbitMultiConj`.  Write `t = m(a, b)`.

**Proved: the general multi-letter case, given a one-letter step.**  Let `C` be an antichain.
Suppose that for every length pair `(ℓ, ℓ')` with `ℓ ≠ ℓ'` realised by a letter of `C`, ONE
canonical letter `m(x₀, y₀)` of that length pair (chosen freely by the Statement) extends the
closure: if `h ∈ H_C` and `h t ∈ S`, then `m(x₀, y₀) h t ∈ S`.  Then `h t ∈ S` holds for EVERY
`h ∈ H_C`, with any number of letters (`higmanVCOrbitMulti_mem_S_of_step`).  The induction runs
on `H_C ≤ ⟨m(x, y) : x, y ∈ C⟩` (left multiplication by letters):
* base: `t ∈ S`, because `t ∈ H_R` for the replicate antichain `R = higmanVCOrbitStem_R a b []`;
* balanced letters (`|x| = |y|`): these lie in `U`, and `U S ⊆ S`;
* unbalanced letters: `m(x, y) = w m(x₀, y₀) w⁻¹` with `w ∈ U ∩ H_C`
  (`higmanVCOrbitMulti_conj`).  Apply the step to `w⁻¹ h`; its IH `w⁻¹ h t ∈ S` follows from
  `U S ⊆ S`;
* inverses: letters are involutions.

**Residual `W⁷` = `HigmanVCOrbitMultiStatement`.**  We prove
`higmanVCOrbitMulti_all_of_multi : W⁷ → W⁗` and `higmanVCOrbitMulti_stem_of_multi : W⁷ → W⁶`.

LOUD, on strength.  `W⁷` is **equivalent to `W⁗` / `W⁶` as a Prop**, and all of them are
Higman-strength.  The converse `higmanVCOrbitMulti_multi_of_all : W⁗ → W⁷` is proved too:
the step's conclusion is again an `h'' t` with `h'' ∈ H_C`.  So `W⁷` is
**NOT strictly weaker**.  It is strictly smaller in PROOF CONTENT:
* only ONE letter per length pair and per antichain (the Statement picks it);
* the IH `h t ∈ S` is handed over;
* balanced letters, conjugate letters, inverses and the induction are all discharged here.
What remains is exactly one multiplicative closure property of `S`: left multiplication by one
unbalanced generator of `H_C`, relative to the pivot `t`, i.e. `m(x₀, y₀) · (S ∩ H_C t) ⊆ S`.

LOUD, the full closure is NOT reached.  `S · S ⊆ S` is equivalent to `S = Q`, i.e. to Higman's
theorem.  The step above is the only multiplicative closure the induction needs.

Truth (given (1) and Claim F of `EnvelopeHigmanVCTreeNFWitPivot`): `S = Q`, so the step
holds.  Checked numerically on `V_2` and `V_3` (`SP/bh-met-92t/multi_step.py`): for random deep
covering antichains `C`, random `h ∈ Sym(C)` and the canonical `m(x₀, y₀)`, the element
`m(x₀, y₀) h t` has a complete antichain `A` whose image is an antichain with the same length
multiset.  The script also checks the permutation identity behind `higmanVCOrbitMulti_conj`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- The canonical one-letter step on `C`. -/
def higmanVCOrbitMulti_Step (d : ℕ) (a b : List (Fin d)) (C : Finset (List (Fin d))) : Prop :=
  ∀ x y : ↥C, x.1.length ≠ y.1.length → ∃ x₀ y₀ : ↥C, x₀.1.length = x.1.length ∧
    y₀.1.length = y.1.length ∧ ∀ h ∈ higmanVCTreeNFWitPivot_H d C,
      h * higmanVCCommon_mk d (FreeGroup.of (a, b)) ∈ higmanVCTreeNFWitPivot_S d →
        higmanVCCommon_mk d (FreeGroup.of (x₀.1, y₀.1)) * h *
          higmanVCCommon_mk d (FreeGroup.of (a, b)) ∈ higmanVCTreeNFWitPivot_S d

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitMulti_Step

/-- The pivot itself lies in `S`. -/
theorem higmanVCOrbitMulti_t_mem_S {d : ℕ} {a b : List (Fin d)} (hab : ¬ a <+: b)
    (hba : ¬ b <+: a) :
    higmanVCCommon_mk d (FreeGroup.of (a, b)) ∈ higmanVCTreeNFWitPivot_S d :=
  higmanVCTreeNFWitPivot_mem_S.mpr ⟨1, (higmanVCTreeNF_U d).one_mem,
    higmanVCOrbitStem_R a b [], higmanVCOrbitStem_R_isAC hab hba [],
    higmanVCCommon_mk d (FreeGroup.of (a, b)), higmanVCOrbitStem_t_mem hab hba, 1,
    (higmanVCTreeNF_U d).one_mem, by rw [one_mul, mul_one]⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitMulti_t_mem_S

/-- **One letter.**  Under the step, every letter of `C` extends the closure. -/
theorem higmanVCOrbitMulti_letter {d : ℕ} {a b : List (Fin d)} {C : Finset (List (Fin d))}
    (hC : higmanVCTreeNFWitPivot_IsAC C) (hs : higmanVCOrbitMulti_Step d a b C) (x y : ↥C)
    {h : higmanVCCommon_Q d} (hh : h ∈ higmanVCTreeNFWitPivot_H d C)
    (ht : h * higmanVCCommon_mk d (FreeGroup.of (a, b)) ∈ higmanVCTreeNFWitPivot_S d) :
    higmanVCCommon_mk d (FreeGroup.of (x.1, y.1)) * h *
      higmanVCCommon_mk d (FreeGroup.of (a, b)) ∈ higmanVCTreeNFWitPivot_S d := by
  by_cases hxy : x.1.length = y.1.length
  · rw [mul_assoc]
    exact higmanVCPivotAC_U_mul_S (higmanVCTreeNF_letter_mem hxy) ht
  obtain ⟨x₀, y₀, hx₀, hy₀, hstep⟩ := hs x y hxy
  have hwU : higmanVCCommon_mk d (FreeGroup.of (y₀.1, y.1)) *
      higmanVCCommon_mk d (FreeGroup.of (x₀.1, x.1)) ∈ higmanVCTreeNF_U d :=
    Subgroup.mul_mem _ (higmanVCTreeNF_letter_mem hy₀) (higmanVCTreeNF_letter_mem hx₀)
  have hwH : higmanVCCommon_mk d (FreeGroup.of (y₀.1, y.1)) *
      higmanVCCommon_mk d (FreeGroup.of (x₀.1, x.1)) ∈ higmanVCTreeNFWitPivot_H d C :=
    Subgroup.mul_mem _ (higmanVCLeafExp_letter_mem_H y₀.2 y.2)
      (higmanVCLeafExp_letter_mem_H x₀.2 x.2)
  have h1 := higmanVCPivotAC_U_mul_S (Subgroup.inv_mem _ hwU) ht
  rw [← mul_assoc] at h1
  have h2 := higmanVCPivotAC_U_mul_S hwU (hstep _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hwH)
    hh) h1)
  rw [← higmanVCOrbitMulti_conj hC hxy hx₀ hy₀]
  simpa only [mul_assoc] using h2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitMulti_letter

/-- **The general multi-letter case.**  Under the step on `C`, `h t ∈ S` for EVERY
`h ∈ H_C`. -/
theorem higmanVCOrbitMulti_mem_S_of_step {d : ℕ} {a b : List (Fin d)} (hab : ¬ a <+: b)
    (hba : ¬ b <+: a) {C : Finset (List (Fin d))} (hC : higmanVCTreeNFWitPivot_IsAC C)
    (hs : higmanVCOrbitMulti_Step d a b C) {h : higmanVCCommon_Q d}
    (hh : h ∈ higmanVCTreeNFWitPivot_H d C) :
    h * higmanVCCommon_mk d (FreeGroup.of (a, b)) ∈ higmanVCTreeNFWitPivot_S d := by
  have hcl := higmanVCOrbitMulti_H_le d C hh
  clear hh
  suffices key : h ∈ higmanVCTreeNFWitPivot_H d C ∧
      h * higmanVCCommon_mk d (FreeGroup.of (a, b)) ∈ higmanVCTreeNFWitPivot_S d from key.2
  induction hcl using Subgroup.closure_induction_left with
  | one =>
    refine ⟨Subgroup.one_mem _, ?_⟩
    rw [one_mul]
    exact higmanVCOrbitMulti_t_mem_S hab hba
  | mul_left g hg k _ ih =>
    obtain ⟨x, y, rfl⟩ := hg
    exact ⟨Subgroup.mul_mem _ (higmanVCLeafExp_letter_mem_H x.2 y.2) ih.1,
      higmanVCOrbitMulti_letter hC hs x y ih.1 ih.2⟩
  | inv_mul_cancel g hg k _ ih =>
    obtain ⟨x, y, rfl⟩ := hg
    rw [higmanVCOrbitMulti_letter_inv]
    exact ⟨Subgroup.mul_mem _ (higmanVCLeafExp_letter_mem_H x.2 y.2) ih.1,
      higmanVCOrbitMulti_letter hC hs x y ih.1 ih.2⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitMulti_mem_S_of_step

/-- The step, required on every deep covering antichain. -/
def higmanVCOrbitMulti_Closed (d L : ℕ) (a b : List (Fin d)) : Prop :=
  ∀ C : Finset (List (Fin d)), higmanVCTreeNFWitPivot_IsAC C → (∀ c ∈ C, L ≤ c.length) →
    (∃ M : ℕ, ∀ w : List (Fin d), w.length = M → ∃ c ∈ C, c <+: w) →
      higmanVCOrbitMulti_Step d a b C

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitMulti_Closed

/-- **Residual W⁷**: the canonical one-letter step.  LOUD: `W⁷ ⇔ W⁗ ⇔ W⁶` as Props
(Higman-strength).  `W⁷` is strictly smaller in proof content only (see the module doc). -/
def HigmanVCOrbitMultiStatement : Prop :=
  ∀ d : ℕ, 1 < d → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ∃ a b : List (Fin d), a.length = n ∧
    b.length = n + 1 ∧ ¬ a <+: b ∧ ¬ b <+: a ∧ higmanVCOrbitMulti_Closed d (n + 1) a b

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.HigmanVCOrbitMultiStatement

/-- **`W⁷ → W⁗`.**  No class exclusion is used: the step closes every `h ∈ H_C`. -/
theorem higmanVCOrbitMulti_all_of_multi (hM : HigmanVCOrbitMultiStatement) :
    HigmanVCOrbitAllStatement := by
  intro d hd N
  obtain ⟨n, hn, a, b, ha, hb, hab, hba, hcl⟩ := hM d hd N
  exact ⟨n, hn, a, b, ha, hb, hab, hba, fun C hC hL hW h hh _ _ =>
    higmanVCOrbitMulti_mem_S_of_step hab hba hC (hcl C hC hL hW) hh⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitMulti_all_of_multi

/-- **`W⁷ → W⁶`.** -/
theorem higmanVCOrbitMulti_stem_of_multi (hM : HigmanVCOrbitMultiStatement) :
    HigmanVCOrbitStemStatement :=
  higmanVCOrbitStem_stem_of_all (higmanVCOrbitMulti_all_of_multi hM)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitMulti_stem_of_multi

/-- **`W⁷ → W''`.** -/
theorem higmanVCOrbitMulti_gap_of_multi (hM : HigmanVCOrbitMultiStatement) :
    HigmanVCOrbitGapStatement :=
  higmanVCOrbitStem_gap_of_stem (higmanVCOrbitMulti_stem_of_multi hM)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitMulti_gap_of_multi

/-- The converse `W⁗ → W⁷` (take `x₀ = x`, `y₀ = y` and discharge the two classes), recorded
to make the Prop-equivalence explicit. -/
theorem higmanVCOrbitMulti_multi_of_all (hA : HigmanVCOrbitAllStatement) :
    HigmanVCOrbitMultiStatement := by
  intro d hd N
  obtain ⟨n, hn, a, b, ha, hb, hab, hba, hcl⟩ := hA d hd N
  have hlen : b.length = a.length + 1 := by rw [ha, hb]
  refine ⟨n, hn, a, b, ha, hb, hab, hba, ?_⟩
  intro C hC hL hW x y _
  refine ⟨x, y, rfl, rfl, ?_⟩
  intro h hh _
  have hh' := Subgroup.mul_mem _ (higmanVCLeafExp_letter_mem_H x.2 y.2) hh
  by_cases hX : higmanVCOrbitGap_Mix d a b (higmanVCCommon_mk d (FreeGroup.of (x.1, y.1)) * h)
  · exact higmanVCOrbitGap_mix_mem_S hab hba hX
  by_cases hY : higmanVCOrbitAll_FamCls d a b (higmanVCCommon_mk d (FreeGroup.of (x.1, y.1)) * h)
  · exact higmanVCOrbitAll_famCls_mem_S hab hba hlen hY
  exact hcl C hC hL hW _ hh' hX hY

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitMulti_multi_of_all

end GroupApproximation.BooneHigman.Metabelian.Envelope
