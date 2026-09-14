import GroupApproximation.GGT.VanKampen.ClosedWalkEnclosedSubdiagram
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketLoopCut
import GroupApproximation.Meta.AxiomGuard

/-!
# The loop cut from the subdiagram enclosed by a closed walk

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): "it is easy to show that `Φ_M` can not
contain loops either.  The only difference is that the subdiagram `Ξ` will be bounded by `st`,
where `l(s) < ε` and `t` is a subpath of `∂Π_1`."

`nonempty_osinLoopCut_of_pocketRegion` (`OsinPocketLoopCut`) builds the loop cut from a pocket
region, whose walk is simple.  In the island case of binder 3 (Case 1 of Lemma 9.4) the side runs
through a cutting path `t` around an island, so the walk uses both darts of the edges of `t` and
the enclosed faces are joined only along `t`.  This file names the loop cut at that generality,
over an enclosed face set (`ClosedWalkEnclosedSubdiagram.EnclosedFaceSet`) in place of a pocket
region.

* `EnclosedSubdiagramLoopCutStatement`: the hypotheses of `nonempty_osinLoopCut_of_pocketRegion`,
  with an enclosed face set and its outside walk in place of the pocket region and its two
  boundary-following conditions, give a loop cut of `Δ`.

The producer composes the enclosed subdiagram (`ClosedWalkEnclosedSubdiagramStatement`), a
geodesic collar along `s` and the transport of regions to `t`.  The named pieces for the collar and
the transport are fixed after lane ms-intro-1's audit of `DiscDiagram.ofPlanar`,
`isRelatorProduct_of_planar`, `Surgery.InnerDiscRegion` and the zero-cell merge.  The consumer is
`OsinLemma94CaseOneIslandStatement` (lane ms-intro-1), through `OsinLoopCut.false_of_below`.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, through Osin's Lemmas 9.4 and 9.7); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded HullSC WordMetric

/-- **The loop cut from an enclosed face set.**  Let `Δ` be least area and `X` an O-equivalent copy
with labels in the symmetric label alphabet.  Take a face set of `X` enclosed by an outside walk,
with a relator cell inside and a cell `i` outside.  Let the inverse walk read a side `s` and an arc
of `i` backwards, with side value of word norm at most `ε`.  Under `C(ε, μ, λ, c, ρ)` with `λ ≤ 1`
and `0 ≤ c`, there is a loop cut of `Δ`. -/
def EnclosedSubdiagramLoopCutStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps rho : ℕ) (mu lambda c : ℝ),
    OsinCCondition D W eps mu lambda c rho → lambda ≤ 1 → 0 ≤ c →
    ∀ (Delta X : DiscDiagram.{u, w, v} W), Delta.LeastArea → OEquivalentDiscDiagram Delta X →
      (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
      ∀ (faces : Finset X.toCombMap.Face) (outerWalk : List X.toCombMap.Dart),
        EnclosedFaceSet X faces outerWalk →
        ∀ C ∈ X.relatorCells, C.face ∈ faces →
        ∀ i : Fin X.rCellCount, (cell X i).face ∉ faces →
        ∀ (A : CyclicArc (cellDarts X i)) (s : List X.toCombMap.Dart),
          invDarts X outerWalk = s ++ invDarts X A.darts →
          wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X s)) ≤ eps →
            Nonempty (OsinLoopCut D lambda c eps Delta)

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.EnclosedSubdiagramLoopCutStatement
