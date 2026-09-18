import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauDecompCross
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauDecompCrossS
import GroupApproximation.Meta.AxiomGuard

/-!
# The decomposition statement on the cross family (lane bh-met-91w)

**Proved outright.**  `higmanVCTauDecomp_cross_decomp`: every instance of the cross family
has a form `sas` decomposition whose three sub-instances are known at level `n`.  The cross
family (`higmanVCTauDecomp_Cross`) is `|p| = 1`, `|q| = 2` and either
`p <+: x ∧ q <+: y` or `p <+: y ∧ q <+: x`.  Write `p = [α]`, `q = [β γ]`; then `α ≠ β`.
Only `d > 1`, `x.length + y.length = n`, the not-all-short hypothesis and the cone images
are used.  None of the negated options is used.

**Reduction.**  `higmanVCTauDecomp_decomp_of_rest`: `higmanVCTauDecomp_RestStatement`
gives `higmanVCTauEqTwo_DecompStatement`.  Then `higmanVCTauDecomp_d2Residual_of_rest` and
`higmanVCTauDecomp_tau_of_rest` go through `higmanVCTauEqTwo_d2Residual_of_decomp`.

**Remaining gap (loud).**  `higmanVCTauDecomp_RestStatement` is
`higmanVCTauEqTwo_DecompStatement` with the extra hypothesis
`¬ higmanVCTauDecomp_Cross p q x y`.
* **Weaker or equal in logical strength**: it has one more hypothesis, so the decomposition
  statement implies it trivially.  With `higmanVCTauDecomp_cross_decomp` it also implies
  the decomposition statement.  So the two are **formally equivalent**.
* **Strictly smaller in proof content**: the cross family is discharged here, and only the
  instances off it remain.
* **Coverage is small (loud).**  In the brute force at `L = 5`, the cross family (both
  orientations) is roughly 2 × 912 of the 28992 residual instances.  The orientation
  `|p| = 2`, `|q| = 1` (the same family with `p ↔ q`) is **not** covered: it would need a
  transport along `coneSwap p q = coneSwap q p`, which is not proved here.
* **Not circular.**  No ConjShort, ShortComplete, TFPShortComplete, CentralBalanced or
  AllAntichain; no witness `X = Q`, `c = id`; no Higman presentation; no `Q ≅ V_d`.

**Truth check (scratch `bh-met-91w/r7.cpp`, exhaustive).**  The explicit decompositions of
`EnvelopeHigmanVCTauDecompCross` were checked on every not-all-short instance of the cross
family with `p <+: x`, residual or not.  Over `{0, 1}` (`d = 2`): `L = 7`: 1248 checked,
0 bad; `L = 9`: 7136 checked, 0 bad.  Over `{0, 1, 2}` (`d = 3`), `L = 5`: 2268 checked,
0 bad.  The swapped orientation (`EnvelopeHigmanVCTauDecompCrossS`) is its mirror image.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- The cross family: `|p| = 1`, `|q| = 2`, and `p, q` are prefixes of `x, y` in some order. -/
def higmanVCTauDecomp_Cross {d : ℕ} (p q x y : List (Fin d)) : Prop :=
  p.length = 1 ∧ q.length = 2 ∧ ((p <+: x ∧ q <+: y) ∨ (p <+: y ∧ q <+: x))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauDecomp_Cross

/-- **The cross family decomposes.**  A form `sas` decomposition with known sub-instances. -/
theorem higmanVCTauDecomp_cross_decomp {d n : ℕ} (hd : 1 < d) {p q x y x' y' : List (Fin d)}
    (hpq : ¬ p <+: q) (hqp : ¬ q <+: p) (hC : higmanVCTauDecomp_Cross p q x y)
    (hx : x.length + y.length = n)
    (hs : ¬ (x.length ≤ 3 ∧ y.length ≤ 3 ∧ x'.length ≤ 3 ∧ y'.length ≤ 3))
    (hmx : MapsCone (coneSwap p q hpq hqp) x x') (hmy : MapsCone (coneSwap p q hpq hqp) y y') :
    higmanVCTauEqTwo_Decomp d n p q x y x' y' hpq hqp := by
  haveI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr (by omega)
  unfold higmanVCTauDecomp_Cross at hC
  obtain ⟨hp1, hq2, hC⟩ := hC
  obtain ⟨α, rfl⟩ := List.length_eq_one_iff.mp hp1
  obtain ⟨β, γ, rfl⟩ := List.length_eq_two.mp hq2
  have hαβ : α ≠ β := fun h => hpq (List.cons_prefix_cons.mpr ⟨h, List.nil_prefix⟩)
  unfold higmanVCTauEqTwo_Decomp
  right
  rcases hC with ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ | ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
  · have ex : x = α :: u := hu.symm
    have ey : y = β :: γ :: v := hv.symm
    subst ex ey
    have ex' : x' = β :: γ :: u :=
      MapsCone.unique hmx ((mapsCone_coneSwap_left hpq hqp).append u)
    have ey' : y' = α :: v := MapsCone.unique hmy ((mapsCone_coneSwap_right hpq hqp).append v)
    subst ex' ey'
    rcases v with _ | ⟨v0, v'⟩
    · rcases u with _ | ⟨u0, u⟩
      · exact (hs ⟨by simp, by simp, by simp, by simp⟩).elim
      · rcases u with _ | ⟨u1, r⟩
        · exact (hs ⟨by simp, by simp, by simp, by simp⟩).elim
        · exact higmanVCTauDecomp_crossNil hd r hαβ hpq hqp hx
    · exact higmanVCTauDecomp_crossNe hd u v' hαβ hpq hqp hx hs
  · have ey : y = α :: u := hu.symm
    have ex : x = β :: γ :: v := hv.symm
    subst ex ey
    have ex' : x' = α :: v := MapsCone.unique hmx ((mapsCone_coneSwap_right hpq hqp).append v)
    have ey' : y' = β :: γ :: u :=
      MapsCone.unique hmy ((mapsCone_coneSwap_left hpq hqp).append u)
    subst ex' ey'
    rcases v with _ | ⟨v0, v'⟩
    · rcases u with _ | ⟨u0, u⟩
      · exact (hs ⟨by simp, by simp, by simp, by simp⟩).elim
      · rcases u with _ | ⟨u1, r⟩
        · exact (hs ⟨by simp, by simp, by simp, by simp⟩).elim
        · exact higmanVCTauDecomp_crossNilS hd r hαβ hpq hqp hx
    · exact higmanVCTauDecomp_crossNeS hd u v' hαβ hpq hqp hx hs

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauDecomp_cross_decomp

/-- **Remaining gap.**  `higmanVCTauEqTwo_DecompStatement` off the cross family: the same
statement with the extra hypothesis `¬ higmanVCTauDecomp_Cross p q x y`.  Weaker or equal in
logical strength (one more hypothesis); formally equivalent to the decomposition statement
by `higmanVCTauDecomp_decomp_of_rest`.  Strictly smaller in proof content: the cross family
is proved outright (`higmanVCTauDecomp_cross_decomp`).  Not proved here. -/
def higmanVCTauDecomp_RestStatement : Prop :=
  ∀ d : ℕ, d = 2 → ∀ n : ℕ,
    ∀ (p q x y x' y' : List (Fin d)) (hpq : ¬ p <+: q) (hqp : ¬ q <+: p),
      ¬ higmanVCTauDecomp_Cross p q x y →
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

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauDecomp_RestStatement

/-- **Reduction.**  The decomposition statement off the cross family gives the full
decomposition statement. -/
theorem higmanVCTauDecomp_decomp_of_rest (h : higmanVCTauDecomp_RestStatement) :
    higmanVCTauEqTwo_DecompStatement := by
  intro d hd n p q x y x' y' hpq hqp hp hq hx hx' hs hOA hOE hOR hFA hFB hFA' hFB' hmx hmy
    hxy hyx hxy' hyx'
  by_cases hC : higmanVCTauDecomp_Cross p q x y
  · exact higmanVCTauDecomp_cross_decomp (by omega) hpq hqp hC hx hs hmx hmy
  · exact h d hd n p q x y x' y' hpq hqp hC hp hq hx hx' hs hOA hOE hOR hFA hFB hFA' hFB' hmx
      hmy hxy hyx hxy' hyx'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauDecomp_decomp_of_rest

/-- **The `d = 2` equal-level residual** from the decomposition statement off the cross
family. -/
theorem higmanVCTauDecomp_d2Residual_of_rest (h : higmanVCTauDecomp_RestStatement) :
    higmanVCTauEqLvl_D2Residual :=
  higmanVCTauEqTwo_d2Residual_of_decomp (higmanVCTauDecomp_decomp_of_rest h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauDecomp_d2Residual_of_rest

/-- **`τ`** from the decomposition statement off the cross family. -/
theorem higmanVCTauDecomp_tau_of_rest (h : higmanVCTauDecomp_RestStatement) :
    HigmanVCTauStatement :=
  higmanVCTauEqTwo_tau_of_decomp (higmanVCTauDecomp_decomp_of_rest h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauDecomp_tau_of_rest

end GroupApproximation.BooneHigman.Metabelian.Envelope
