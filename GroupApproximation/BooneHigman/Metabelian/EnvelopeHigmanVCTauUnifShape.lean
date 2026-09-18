import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauUnifHop
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauUnifSwap
import GroupApproximation.Meta.AxiomGuard

/-!
# The shape of the deep residual (lane bh-met-77y)

`higmanVCTauUnif_Shape d p q x y`: `x = a`, `y = z c t` with `t` nonempty, `z`, `zo`
incomparable of length two and not starting with `a`, and `{p, q} = {z c, zo c'}`.
`higmanVCTauUnif_shape_hops` proves that every such instance satisfies Hop D (`c = c'`) or
Hop CD (`c ≠ c'`), by the uniform witnesses of `EnvelopeHigmanVCTauUnifHop`.

`HigmanVCTauUnifClassifyStatement` says that every instance that escapes the options, the
flexible squares, Hop A and Hop C has this shape (up to swapping `x`, `y`).
`higmanVCTauUnif_deep_of_classify` proves the deep residual from it.

**Strength (LOUD): the gap is NOT a weaker proposition.**  It IMPLIES
`HigmanVCTauDeepResidualStatement` (proved here) and is not implied by it: it drops the
hypotheses `Below`, `Shrink`, the chain and Hop D / Hop CD negations, and replaces the
conclusion `conjEq` by the purely combinatorial `Shape`.  So it is a STRONGER (or at best
incomparable) statement, with **strictly smaller proof content**: no `ψ`, no conjugacy, no
`Below` / `Shrink`, only prefix combinatorics of finitely many short words.  The obvious
weaker alternative, "Deep plus `¬ Shape`", is EQUIVALENT to Deep and was rejected.

**Truth check** (scratch `SP/bh-met-77y/res.cpp`, `unif.py`; not proved for all `d`, `n`).
* Equal-level instances escaping the options and flexible squares, then Hop A / Hop C:
  `d = 2`, words `≤ 5`: 28992, left 384; `≤ 6`: 124736, left 896; `≤ 7`: 512832, left 1920
  (480 orbit representatives).  Every left instance is in `Shape` (0 outside).
  `d = 3`, words `≤ 6`, and `d = 4`, words `≤ 4`: nothing escapes (vacuous).
* `unif.py` checks the uniform Hop D / Hop CD witnesses on every `Shape` instance:
  `d = 2` words `≤ 7`, `d = 3` words `≤ 6`, `d = 4` words `≤ 5`: 0 failures.
The python hops demand at least what the Lean hops demand, so the Lean residual lies inside the
python one.  Caveat: the python filter for Option A is the scratch `genFA` along the step pair,
matching `higmanVCTauShort_OptionA` by the lane bh-met-77t correspondence (not re-proved).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- The shape of the deep residual: `x = a`, `y = z c t`, `{p, q} = {z c, zo c'}`. -/
def higmanVCTauUnif_Shape (d : ℕ) (p q x y : List (Fin d)) : Prop :=
  ∃ (a c c' t0 : Fin d) (z zo t1 : List (Fin d)),
    z.length = 2 ∧ zo.length = 2 ∧ higmanVCTauUnif_Inc z zo ∧ higmanVCTauUnif_Inc [a] z ∧
      higmanVCTauUnif_Inc [a] zo ∧ x = [a] ∧ y = z ++ [c] ++ (t0 :: t1) ∧
      ((p = z ++ [c] ∧ q = zo ++ [c']) ∨ (p = zo ++ [c'] ∧ q = z ++ [c]))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauUnif_Shape

/-- **Shape instances hop.**  Hop D if the marked letters agree, Hop CD otherwise. -/
theorem higmanVCTauUnif_shape_hops {d n : ℕ} (hd : 1 < d) {p q x y x' y' : List (Fin d)}
    {hpq : ¬ p <+: q} {hqp : ¬ q <+: p} (hS : higmanVCTauUnif_Shape d p q x y)
    (hn : x.length + y.length = n) (hmx : MapsCone (coneSwap p q hpq hqp) x x')
    (hmy : MapsCone (coneSwap p q hpq hqp) y y') :
    higmanVCTauDeep_HopD d n p q x y x' y' ∨ higmanVCTauDeep_HopCD d n p q x y x' y' := by
  haveI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr (by omega)
  obtain ⟨a, c, c', t0, z, zo, t1, hz, hzo, hzz, haz, hazo, rfl, rfl, hs⟩ := hS
  have hRa := higmanVCTauUnif_incR [c] haz
  have hSa := higmanVCTauUnif_incR [c'] hazo
  have hzoz := higmanVCTauUnif_incS hzz
  rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · obtain rfl : x' = [a] := MapsCone.unique hmx (higmanVCTauUnif_fix hpq hqp hRa hSa)
    obtain rfl : y' = zo ++ [c'] ++ (t0 :: t1) :=
      MapsCone.unique hmy ((mapsCone_coneSwap_left hpq hqp).append (t0 :: t1))
    by_cases hcc : c = c'
    · subst hcc
      exact Or.inl (higmanVCTauUnif_hopD (p0 := z) (q0 := zo) hd hz hzo hzz haz hazo
        (Or.inl ⟨rfl, rfl⟩) hn)
    · exact Or.inr (higmanVCTauUnif_hopCD (p0 := z) (q0 := zo) hd hz hzo hzz haz hazo hcc
        (Or.inl ⟨rfl, rfl⟩) (mapsCone_coneSwap_left _ _)
        (higmanVCTauUnif_fix _ _ (higmanVCTauUnif_incB [c'] [c] hzoz)
          (higmanVCTauUnif_incB [c'] [c'] hzoz)) hn)
  · obtain rfl : x' = [a] := MapsCone.unique hmx (higmanVCTauUnif_fix hpq hqp hSa hRa)
    obtain rfl : y' = zo ++ [c'] ++ (t0 :: t1) :=
      MapsCone.unique hmy ((mapsCone_coneSwap_right hpq hqp).append (t0 :: t1))
    by_cases hcc : c = c'
    · subst hcc
      exact Or.inl (higmanVCTauUnif_hopD (p0 := zo) (q0 := z) hd hz hzo hzz haz hazo
        (Or.inr ⟨rfl, rfl⟩) hn)
    · exact Or.inr (higmanVCTauUnif_hopCD (p0 := zo) (q0 := z) hd hz hzo hzz haz hazo hcc
        (Or.inr ⟨rfl, rfl⟩)
        (higmanVCTauUnif_fix _ _ (higmanVCTauUnif_incB [c'] [c] hzoz)
          (higmanVCTauUnif_incB [c'] [c'] hzoz)) (mapsCone_coneSwap_left _ _) hn)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauUnif_shape_hops

/-- **Remaining gap (classification).**  An equal-level instance escaping the options, the
flexible squares, Hop A and Hop C has the shape `higmanVCTauUnif_Shape` (up to swapping `x`,
`y`).  **STRONGER than / not implied by** the deep residual; strictly smaller proof content
(pure prefix combinatorics).  See the module docstring. -/
def HigmanVCTauUnifClassifyStatement : Prop :=
  ∀ d : ℕ, 1 < d → ∀ n : ℕ,
    ∀ (p q x y x' y' : List (Fin d)) (hpq : ¬ p <+: q) (hqp : ¬ q <+: p),
      p.length ≤ 3 → q.length ≤ 3 →
      x.length + y.length = n → x'.length + y'.length = n →
      ¬ (x.length ≤ 3 ∧ y.length ≤ 3 ∧ x'.length ≤ 3 ∧ y'.length ≤ 3) →
      ¬ higmanVCTauShort_OptionA d p q x y hpq hqp →
      ¬ higmanVCTauShort_OptionE d p q x y →
      ¬ higmanVCTauComm_OptionR d p q x y →
      ¬ higmanVCTauComm_FlexA d p q x y hpq hqp → ¬ higmanVCTauComm_FlexB d p q x y x' y' →
      ¬ higmanVCTauComm_FlexA d p q x' y' hpq hqp →
      ¬ higmanVCTauComm_FlexB d p q x' y' x y →
      ¬ higmanVCTauLevel_HopA d n p q x y x' y' hpq hqp →
      ¬ higmanVCTauLevel_HopA d n p q x' y' x y hpq hqp →
      ¬ higmanVCTauLevel_HopC d n p q x y x' y' →
      MapsCone (coneSwap p q hpq hqp) x x' → MapsCone (coneSwap p q hpq hqp) y y' →
      ¬ x <+: y → ¬ y <+: x → ¬ x' <+: y' → ¬ y' <+: x' →
      higmanVCTauUnif_Shape d p q x y ∨ higmanVCTauUnif_Shape d p q y x

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.HigmanVCTauUnifClassifyStatement

/-- **Reduction.**  The classification makes the deep residual vacuous. -/
theorem higmanVCTauUnif_deep_of_classify (h : HigmanVCTauUnifClassifyStatement) :
    HigmanVCTauDeepResidualStatement := by
  intro d hd n _ p q x y x' y' hpq hqp hp hq hA _ _ hs hOA hE hR hF _ hn h1 h2 h3 h4 _ h6 hmx
    hmy hxy hyx hxy' hyx'
  exfalso
  obtain ⟨f1, f2, f3, f4⟩ := hF hn
  rcases h d hd n p q x y x' y' hpq hqp hp hq hA hn hs hOA hE hR f1 f2 f3 f4 h1 h2 h3 hmx hmy
    hxy hyx hxy' hyx' with hS | hS
  · rcases higmanVCTauUnif_shape_hops hd hS hA hmx hmy with hH | hH
    · exact h4 hH
    · exact h6 hH
  · rcases higmanVCTauUnif_shape_hops hd hS (by omega) hmy hmx with hH | hH
    · exact h4 (higmanVCTauUnif_hopD_swap hH)
    · exact h6 (higmanVCTauUnif_hopCD_swap hH)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauUnif_deep_of_classify

/-- **Wire.**  The `τ` half from the classification and the lower-level part. -/
theorem higmanVCTauUnif_tau_of_classify (h : HigmanVCTauUnifClassifyStatement)
    (hLt : HigmanVCTauLevelLtStatement) : HigmanVCTauStatement :=
  higmanVCTauDeep_tau_of_deep (higmanVCTauUnif_deep_of_classify h) hLt

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauUnif_tau_of_classify

end GroupApproximation.BooneHigman.Metabelian.Envelope
