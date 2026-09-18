import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCOrbitLongSwap
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCOrbitAllReduce
import Mathlib.Tactic.Group
import GroupApproximation.Meta.AxiomGuard

/-!
# Residual `W⁵`: the gap closure off the long-swap class (lane bh-met-92d)

Notation as in `EnvelopeHigmanVCOrbitAllReduce`.

**Proved.**  The long-swap class `higmanVCOrbitLong_Cls` holds the elements
`u · m(a q y, b q y r i) · (t v t⁻¹)` and `u · m(a q y r i, b q y) · (t v t⁻¹)`, where
`u, v ∈ U`, `q, r` are arbitrary words and `j ≠ y` is a letter.  Each `h` in this class
satisfies `h t ∈ S` (`higmanVCOrbitLong_cls_mem_S`, from `EnvelopeHigmanVCOrbitLongSwap`).
In particular, every comparable single swap `m(a e, b e')` with `e ≠ e'` both nonempty lies
in it, for every `k = |e'| - |e|`.

**Residual `W⁵` = `HigmanVCOrbitLongStatement`.**  This is `HigmanVCOrbitAllStatement`
(`W⁗`), with the pivot closure also dropped on `higmanVCOrbitLong_Cls`.  We prove
`higmanVCOrbitLong_all_of_long : W⁵ → W⁗` and `higmanVCOrbitLong_gap_of_long : W⁵ → W''`.

LOUD, on strength: `W⁵ ⇔ W⁗ ⇔ W''` as Props (`higmanVCOrbitLong_long_of_all` is the trivial
converse), and all of them are Higman-strength.  `W⁵` is strictly smaller in PROOF CONTENT
only.  No class-exclusion residual can be strictly weaker as a Prop, because the excluded
classes are proved outright.

LOUD, the open single swaps: these are the swaps with an EMPTY stem, `m(a, b e')` with
`|e'| ≥ 3` and its twist `m(a e, b)` with `|e| ≥ 3`.  `|k| ≤ 2` is handled by
`EnvelopeHigmanVCOrbitAllSwap2`.  For these swaps, `U`-conjugation stays inside the cones
`a·`, `b·`, so it cannot create a stem.  The natural identity
`m(a, b y r) t = L⁻¹ (t P t⁻¹) t w`, with `L = m(a, b y)`, `w = m(b, a y)` and
`P = m(a y, b r)`, only reproduces a swap of the same empty-stem shape after the long-swap
decomposition of `P` is substituted.  So it is circular.  Beyond the single swaps, the
general multi-letter `h` is untouched.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- The group identity behind the class discharge. -/
theorem higmanVCOrbitLong_cls_eq {G : Type*} [Group G] (u σ t v : G) :
    u * σ * (t * v * t⁻¹) * t = u * (σ * t) * v := by group

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitLong_cls_eq

/-- The long-swap class: `u · σ · (t v t⁻¹)` with `u, v ∈ U` and `σ` a long swap
`m(a q y, b q y r i)` or a twisted long swap `m(a q y r i, b q y)`, where `j ≠ y`. -/
def higmanVCOrbitLong_Cls (d : ℕ) (a b : List (Fin d)) (h : higmanVCCommon_Q d) : Prop :=
  ∃ u ∈ higmanVCTreeNF_U d, ∃ v ∈ higmanVCTreeNF_U d, ∃ (q r : List (Fin d)) (y j i : Fin d),
    j ≠ y ∧
      (h = u * higmanVCCommon_mk d (FreeGroup.of (a ++ q ++ [y], b ++ q ++ [y] ++ r ++ [i])) *
          (higmanVCCommon_mk d (FreeGroup.of (a, b)) * v *
            (higmanVCCommon_mk d (FreeGroup.of (a, b)))⁻¹) ∨
        h = u * higmanVCCommon_mk d (FreeGroup.of (a ++ q ++ [y] ++ r ++ [i], b ++ q ++ [y])) *
          (higmanVCCommon_mk d (FreeGroup.of (a, b)) * v *
            (higmanVCCommon_mk d (FreeGroup.of (a, b)))⁻¹))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitLong_Cls

/-- **Class discharge.**  Every `h` in the long-swap class satisfies `h t ∈ S`. -/
theorem higmanVCOrbitLong_cls_mem_S {d : ℕ} {a b : List (Fin d)} (hab : ¬ a <+: b)
    (hba : ¬ b <+: a) {h : higmanVCCommon_Q d} (hh : higmanVCOrbitLong_Cls d a b h) :
    h * higmanVCCommon_mk d (FreeGroup.of (a, b)) ∈ higmanVCTreeNFWitPivot_S d := by
  obtain ⟨u, hu, v, hv, q, r, y, j, i, hj, rfl | rfl⟩ := hh
  · rw [higmanVCOrbitLong_cls_eq]
    exact higmanVCTreeNFWitPivot_S_mul_U
      (higmanVCPivotAC_U_mul_S hu (higmanVCOrbitLong_swap_mem_S hab hba q r hj i)) hv
  · rw [higmanVCOrbitLong_cls_eq]
    exact higmanVCTreeNFWitPivot_S_mul_U
      (higmanVCPivotAC_U_mul_S hu (higmanVCOrbitLong_swap'_mem_S hab hba q r hj i)) hv

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitLong_cls_mem_S

/-- The pivot closure, required only for `h` that is not mixed, not in the path-atom class
and not in the long-swap class. -/
def higmanVCOrbitLong_Closed (d L : ℕ) (a b : List (Fin d)) : Prop :=
  ∀ C : Finset (List (Fin d)), higmanVCTreeNFWitPivot_IsAC C → (∀ c ∈ C, L ≤ c.length) →
    (∃ M : ℕ, ∀ w : List (Fin d), w.length = M → ∃ c ∈ C, c <+: w) →
      ∀ h ∈ higmanVCTreeNFWitPivot_H d C, ¬ higmanVCOrbitGap_Mix d a b h →
        ¬ higmanVCOrbitAll_FamCls d a b h → ¬ higmanVCOrbitLong_Cls d a b h →
          h * higmanVCCommon_mk d (FreeGroup.of (a, b)) ∈ higmanVCTreeNFWitPivot_S d

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitLong_Closed

/-- **Residual W⁵**: the pivot closure off the mixed, path-atom and long-swap classes.
LOUD: `W⁵ ⇔ W⁗ ⇔ W''` as Props.  `W⁵` is strictly smaller in proof content only. -/
def HigmanVCOrbitLongStatement : Prop :=
  ∀ d : ℕ, 1 < d → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ∃ a b : List (Fin d), a.length = n ∧
    b.length = n + 1 ∧ ¬ a <+: b ∧ ¬ b <+: a ∧ higmanVCOrbitLong_Closed d (n + 1) a b

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.HigmanVCOrbitLongStatement

/-- **`W⁵ → W⁗`.** -/
theorem higmanVCOrbitLong_all_of_long (hL : HigmanVCOrbitLongStatement) :
    HigmanVCOrbitAllStatement := by
  intro d hd N
  obtain ⟨n, hn, a, b, ha, hb, hab, hba, hcl⟩ := hL d hd N
  refine ⟨n, hn, a, b, ha, hb, hab, hba, ?_⟩
  intro C hC hL' hM h hh hX hY
  by_cases hZ : higmanVCOrbitLong_Cls d a b h
  · exact higmanVCOrbitLong_cls_mem_S hab hba hZ
  · exact hcl C hC hL' hM h hh hX hY hZ

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitLong_all_of_long

/-- **`W⁵ → W''`.** -/
theorem higmanVCOrbitLong_gap_of_long (hL : HigmanVCOrbitLongStatement) :
    HigmanVCOrbitGapStatement :=
  higmanVCOrbitAll_gap_of_all (higmanVCOrbitLong_all_of_long hL)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitLong_gap_of_long

/-- The trivial converse `W⁗ → W⁵`, recorded to make the Prop-equivalence explicit. -/
theorem higmanVCOrbitLong_long_of_all (hA : HigmanVCOrbitAllStatement) :
    HigmanVCOrbitLongStatement := by
  intro d hd N
  obtain ⟨n, hn, a, b, ha, hb, hab, hba, hcl⟩ := hA d hd N
  exact ⟨n, hn, a, b, ha, hb, hab, hba, fun C hC hL hM h hh hX hY _ => hcl C hC hL hM h hh hX hY⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitLong_long_of_all

end GroupApproximation.BooneHigman.Metabelian.Envelope
