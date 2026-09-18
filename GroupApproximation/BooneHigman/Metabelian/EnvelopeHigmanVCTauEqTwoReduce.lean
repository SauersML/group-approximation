import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauEqTwoSquare
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauEqLvlD2
import GroupApproximation.Meta.AxiomGuard

/-!
# The `d = 2` equal-level residual, modulo a word-combinatorial statement (lane bh-met-91q)

**Proved.**  `higmanVCTauEqTwo_d2Residual_of_decomp`: `higmanVCTauEqTwo_DecompStatement`
gives `higmanVCTauEqLvl_D2Residual`.  Every residual instance `(s; A → B)` is split through a
short pair `a` into three sub-instances known at level `n` (form `aba` or form `sas`,
`EnvelopeHigmanVCTauEqTwoSquare`).  Then `higmanVCTauEqTwo_tau_of_decomp` and
`higmanVCTauEqTwo_fpMetabelian_of_decomp` give the `τ` input and the BH root.

**Remaining gap (loud).**  `higmanVCTauEqTwo_DecompStatement`: every instance of the `d = 2`
equal-level residual has a form `aba` or form `sas` decomposition whose three sub-instances
are known at level `n`.
* **Strictly smaller in proof content.**  It is pure word combinatorics.  It mentions only
  words, cone swaps as permutations of Cantor space, lengths and the option predicates.  It
  has no group `higmanVC_Q`, no `ψ` and no induction hypotheses `Below`/`Shrink`.  All the
  group theory (all-short relators, the three sub-instances, the two conjugation identities)
  is proved here.
* **Not comparable in logical strength**, and it is **not** a restatement.  It is not
  formally implied by `higmanVCTauEqLvl_D2Residual`, which is a statement in a group.  It is
  a finite-shape statement about words: the options, the cone images and the length
  comparisons depend only on bounded prefixes of the words and on differences of lengths.
* **Not claimed equivalent**, and not proved here.
* **Not circular.**  It does not use ConjShort, ShortComplete, TFPShortComplete,
  CentralBalanced or AllAntichain.  It does not use the witness `X = Q`, `c = id`, Higman's
  presentation or `Q ≅ V_d`.

**Truth check (scratch `bh-met-91q/dec4.cpp`, exhaustive).**  Instances are all short
`s = (p, q)` and all words `x, y` of length `≤ L` over `{0, 1}`.  The equal-level residual
keeps the instances where the options and flexible A/B on both sides all fail.
* `L = 4`: 5696 residual instances of 52544 equal-level ones;
* `L = 5`: 28992 of 300864;
* `L = 6`: 124736 of 1388864.
Every residual instance has a decomposition: 0 left for `L = 4, 5, 6`.  The form `aba` alone
leaves 1664 at `L = 4` and 7680 at `L = 5`.  So both forms are needed.  Sub-instances known
only through "one side below `n`" or "all short" are not enough either: 5312 are left at
`L = 4`.  Level-`n` options on sub-instances are used.  The model of `MapsCone (coneSwap P Q)`
is: prefix replacement on the cones of `P` and `Q`, the identity off both cones, and no image
for a proper prefix of `P` or `Q`.  Example (`aba`): `s = (000, 001)`, `A = (1, 0100)`,
`a = (1, 010)`, `b = (000, 001)`, `A1 = A2 = (010, 10)`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- A form `aba` or form `sas` decomposition with known sub-instances at level `n`. -/
def higmanVCTauEqTwo_Decomp (d n : ℕ) (p q x y x' y' : List (Fin d)) (hpq : ¬ p <+: q)
    (hqp : ¬ q <+: p) : Prop :=
  higmanVCTauEqTwo_Aba d n p q x y x' y' ∨ higmanVCTauEqTwo_Sas d n p q x y x' y' hpq hqp

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauEqTwo_Decomp

/-- **Remaining gap (word combinatorics).**  Every `d = 2` equal-level residual instance has
a decomposition (`higmanVCTauEqTwo_Decomp`).  Strictly smaller in proof content than
`higmanVCTauEqLvl_D2Residual`: it has no group theory.  Not proved here.  Brute force: true
for words of length `≤ 6`. -/
def higmanVCTauEqTwo_DecompStatement : Prop :=
  ∀ d : ℕ, d = 2 → ∀ n : ℕ,
    ∀ (p q x y x' y' : List (Fin d)) (hpq : ¬ p <+: q) (hqp : ¬ q <+: p),
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

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauEqTwo_DecompStatement

/-- **Reduction.**  The decomposition statement gives the `d = 2` equal-level residual. -/
theorem higmanVCTauEqTwo_d2Residual_of_decomp (h : higmanVCTauEqTwo_DecompStatement) :
    higmanVCTauEqLvl_D2Residual := by
  intro d hd n hB p q x y x' y' hpq hqp hp hq hx hx' hSh hs hOA hOE hOR hFA hFB hFA' hFB'
    hmx hmy hxy hyx hxy' hyx'
  have hd1 : 1 < d := by omega
  have hD := h d hd n p q x y x' y' hpq hqp hp hq hx hx' hs hOA hOE hOR hFA hFB hFA' hFB' hmx
    hmy hxy hyx hxy' hyx'
  unfold higmanVCTauEqTwo_Decomp at hD
  rcases hD with hD | hD
  · exact higmanVCTauEqTwo_aba hd1 hB hSh hpq hqp hp hq hxy hyx hxy' hyx' hD
  · exact higmanVCTauEqTwo_sas hd1 hB hSh hpq hqp hp hq hxy hyx hxy' hyx' hD

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauEqTwo_d2Residual_of_decomp

/-- **`τ` from the decomposition statement.** -/
theorem higmanVCTauEqTwo_tau_of_decomp (h : higmanVCTauEqTwo_DecompStatement) :
    HigmanVCTauStatement :=
  higmanVCTauEqLvl_tau_of_d2 (higmanVCTauEqTwo_d2Residual_of_decomp h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauEqTwo_tau_of_decomp

/-- **BH root** with `hB` taken from the decomposition statement. -/
theorem higmanVCTauEqTwo_fpMetabelian_of_decomp
    (hH : Absorption.SuslinLocalHorrocksStatement)
    (hvdk : ElemFP.VdKRowExtensionStatement)
    (hloc : ElemFP.PolyK2CubeNilLocalStatement)
    (hgen : ElemFPCharZero.CharZeroK2PosStabGenStatement)
    (hcube : ElemFPCharZero.CharZeroK2CubeGapPosStatement)
    (hO : HigmanVCOrbitStatement)
    (h : higmanVCTauEqTwo_DecompStatement) :
    FinitelyPresentedMetabelianStatement :=
  higmanVCTauEqLvl_fpMetabelian_of_d2 hH hvdk hloc hgen hcube hO
    (higmanVCTauEqTwo_d2Residual_of_decomp h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauEqTwo_fpMetabelian_of_decomp

end GroupApproximation.BooneHigman.Metabelian.Envelope
