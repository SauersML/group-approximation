import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalArcEndRule
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalArcEndExists
import GroupApproximation.Meta.AxiomGuard

/-!
# The single-run case of the arc-end surgery rule, proved outright

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-30.

`ExtremalArcEndRuleSingleRunStatement` (lane gl-p10-27, `Piece10Live/ExtremalArcEndRule`) is
proved here with no open hypothesis: `extremalJordanReroute_singleRun`.

## Proof

Let `z` be the extra exterior class and split the pocket walk as `A ++ d :: (B ++ e :: C)` with
`d`, `e` kept, every dart of `B` removed and every dart of `A ++ C` kept.  This is exactly the
shape of the parity lemma `extremalArcEndExists_closed_run_pocket` (lane gl-p10-25,
`Piece10Live/ExtremalArcEndExists`) for the class `r := z`: its `kept` predicate is
`P10ExtremalResidual.keptPred K z`, the predicate of the statement, and it needs only
`K.ClosedWalk`.  The hypothesis on `A ++ C` splits into one on `A` and one on `C`.  None of the
other premises is used: not the pattern of the linked class `r`, not `z` being an extra exterior
class, not least area.  So the statement holds for every class whose removed walk darts form one
inner run (the balance argument noted by lane gl-p10-27).

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove

/-- **The single-run case (A) of the surgery rule**: a lone inner removed run of any class is
linked, by the parity count at a vertex. -/
theorem extremalJordanReroute_singleRun :
    ExtremalArcEndRuleSingleRunStatement.{u, w, v} := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ K hK _ _ _ _ _ _ _ _ z _ A d B e C hcyc hd he hB _ hAC
  exact extremalArcEndExists_closed_run_pocket K hK z hcyc
    (fun x hx => hAC x (List.mem_append_left C hx)) hd hB he
    (fun x hx => hAC x (List.mem_append_right A hx))

/-- **Case (A) restricted to one inner run, without the linked-class premises**: under
`K.ClosedWalk` alone, a class whose removed walk darts are exactly one inner run between kept
darts `d` and `e` has linked ends. -/
theorem extremalJordanReroute_singleRun_linked {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} {D : RelGenSet G Lambda} {eps : ℕ}
    {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ} (K : PocketFaceSet D eps X lo hi)
    (hK : K.ClosedWalk) (z : X.toCombMap.Dart) {A B C : List X.toCombMap.Dart}
    {d e : X.toCombMap.Dart} (hcyc : K.boundary.cycle = A ++ d :: (B ++ e :: C))
    (hd : P10ExtremalResidual.keptPred K z d = true)
    (he : P10ExtremalResidual.keptPred K z e = true)
    (hB : ∀ x ∈ B, P10ExtremalResidual.keptPred K z x = false)
    (hAC : ∀ x ∈ A ++ C, P10ExtremalResidual.keptPred K z x = true) :
    X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e :=
  extremalArcEndExists_closed_run_pocket K hK z hcyc
    (fun x hx => hAC x (List.mem_append_left C hx)) hd hB he
    (fun x hx => hAC x (List.mem_append_right A hx))

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanReroute_singleRun
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanReroute_singleRun_linked
