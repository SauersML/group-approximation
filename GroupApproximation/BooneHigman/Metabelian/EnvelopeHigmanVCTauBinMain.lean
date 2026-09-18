import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauBinCases
import GroupApproximation.Meta.AxiomGuard

/-!
# The binary classification outside the hop families (lane bh-met-78b)

`higmanVCTauBin_good`: over `Fin 2`, every equal-level instance of a cone swap `(p, q)` with
`|p|, |q| ≤ 3`, not all short, with incomparable source words, has a flexible square
(`higmanVCTauClassify_Good`) or is a `higmanVCTauUnif_Shape` instance, unless it lies in one
of the two *hop families* `higmanVCTauBin_Hop`:
* (F1) both source words lie in the cones of `p`, `q` and `|p| + |q| = 3`;
* (F2) both source words are fixed and `|p| = |q| = 3`.
So `HigmanVCTauClassifyTwoStatement` reduces to `HigmanVCTauBinHopStatement`, its restriction
to the hop families (`higmanVCTauBin_classifyTwo_of_hop`).

**Strength (LOUD): the residual is a proper special case, hence only EQUIVALENT as a
proposition, not strictly weaker.**  `HigmanVCTauBinHopStatement` is the target with the one
extra hypothesis `higmanVCTauBin_Hop p q x y`, so the target implies it trivially; with
`higmanVCTauBin_classifyTwo_of_hop` the two are logically equivalent (as is any true special
case).  The instances removed are all binary instances outside F1 ∪ F2 (every position case
`PP`, `QQ`, `PF`, `QF`, `FP`, `FQ`; `PQ` / `QP` with `|p| + |q| ≠ 3`; `FF` unless
`|p| = |q| = 3`).  On F1 ∪ F2 the witness plan has no flexible square; there the target's
contradiction has to come from `HopA` / `HopC`, which involve level-`n` `Easy` squares.
(F1 is stated generously: its `PQ` instances with `p`, `q` sharing a first letter are in
fact covered by `higmanVCTauBin_casePQ`, but are left in the residual.)

**Truth check.**  The witness plan of `EnvelopeHigmanVCTauBinFlex` / `...Cases` was checked by
scratch `SP/bh-met-78b/plan2.cpp` over `Fin 2`, words `≤ 7`: 0 failures outside F1 ∪ F2
(the `FP` leftover being exactly `Shape`).  The residual is the lane bh-met-77y claim
restricted to F1 ∪ F2, which bh-met-77y checked at `d = 2` for words `≤ 7`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- The two hop families over `Fin 2`: (F1) `|p| + |q| = 3` with both source words in the
cones; (F2) `|p| = |q| = 3` with both source words fixed. -/
def higmanVCTauBin_Hop (p q x y : List (Fin 2)) : Prop :=
  (p.length + q.length = 3 ∧ (p <+: x ∨ q <+: x) ∧ (p <+: y ∨ q <+: y)) ∨
    (p.length = 3 ∧ q.length = 3 ∧ higmanVCTauUnif_Inc x p ∧ higmanVCTauUnif_Inc x q ∧
      higmanVCTauUnif_Inc y p ∧ higmanVCTauUnif_Inc y q)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauBin_Hop

end GroupApproximation.BooneHigman.Metabelian.Envelope
