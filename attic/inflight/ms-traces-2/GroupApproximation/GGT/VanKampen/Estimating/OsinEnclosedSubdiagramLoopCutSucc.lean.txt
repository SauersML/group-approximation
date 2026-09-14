import GroupApproximation.GGT.VanKampen.ClosedWalkEnclosedSucc
import GroupApproximation.GGT.VanKampen.Estimating.OsinEnclosedSubdiagramLoopCut
import GroupApproximation.Meta.AxiomGuard

/-!
# The loop cut from an enclosed face set whose outside walk turns to its successor

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): "it is easy to show that `Φ_M` can not
contain loops either.  The only difference is that the subdiagram `Ξ` will be bounded by `st`,
where `l(s) < ε` and `t` is a subpath of `∂Π_1`."

`EnclosedSubdiagramLoopCutStatement` (`OsinEnclosedSubdiagramLoopCut`) takes an `EnclosedFaceSet`,
whose turning condition does not fix the order of the outside walk (`ClosedWalkEnclosedSucc`).
This module names the loop cut over `EnclosedFaceSetSucc`, additively.

* `EnclosedSubdiagramLoopCutSuccStatement`: the hypotheses of `EnclosedSubdiagramLoopCutStatement`,
  with an outside walk that turns to its successor, give a loop cut of `Δ`.
* `enclosedSubdiagramLoopCutSucc_of_loopCut`: the unsuffixed statement gives the successor form.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, "Hull's small cancellation theorem", through Osin's
Lemmas 9.4 and 9.7); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded HullSC WordMetric

/-- **The loop cut from an enclosed face set whose outside walk turns to its successor.**  Let `Δ`
be least area and `X` an O-equivalent copy with labels in the symmetric label alphabet.  Take a face
set of `X` enclosed by an outside walk that turns to its successor, with a relator cell inside and a
cell `i` outside.  Let the inverse walk read a side `s` and an arc of `i` backwards, with side value
of word norm at most `ε`.  Under `C(ε, μ, λ, c, ρ)` with `λ ≤ 1` and `0 ≤ c`, there is a loop cut of
`Δ`. -/
def EnclosedSubdiagramLoopCutSuccStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps rho : ℕ) (mu lambda c : ℝ),
    OsinCCondition D W eps mu lambda c rho → lambda ≤ 1 → 0 ≤ c →
    ∀ (Delta X : DiscDiagram.{u, w, v} W), Delta.LeastArea → OEquivalentDiscDiagram Delta X →
      (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
      ∀ (faces : Finset X.toCombMap.Face) (outerWalk : List X.toCombMap.Dart),
        EnclosedFaceSetSucc X faces outerWalk →
        ∀ C ∈ X.relatorCells, C.face ∈ faces →
        ∀ i : Fin X.rCellCount, (cell X i).face ∉ faces →
        ∀ (A : CyclicArc (cellDarts X i)) (s : List X.toCombMap.Dart),
          invDarts X outerWalk = s ++ invDarts X A.darts →
          wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X s)) ≤ eps →
            Nonempty (OsinLoopCut D lambda c eps Delta)

/-- The unsuffixed enclosed loop cut statement gives the successor form. -/
theorem enclosedSubdiagramLoopCutSucc_of_loopCut
    (h : EnclosedSubdiagramLoopCutStatement.{u, w, v}) :
    EnclosedSubdiagramLoopCutSuccStatement.{u, w, v} := by
  intro G _ Lambda W D eps rho mu lambda c hcond hlambda hc Delta X hlea equiv hlabel faces
    outerWalk hE
  exact h D eps rho mu lambda c hcond hlambda hc Delta X hlea equiv hlabel faces outerWalk
    hE.toEnclosedFaceSet

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.EnclosedSubdiagramLoopCutSuccStatement
#audit_axioms GroupApproximation.GGT.VanKampen.enclosedSubdiagramLoopCutSucc_of_loopCut
