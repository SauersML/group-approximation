import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.NoWalkAbsorbLemmas
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-35: the target from the whole-pocket residual

* `FourPieceWitness.noPlanarDegenStep_of_noWalkAbsorb`: `NoWalkAbsorbStatement` implies
  `NoPlanarDegenStepStatement`.  On the LEFT disjunct the face set is the whole pocket
  `sideFaces K.walk`.  Clause 2 comes from the dart clause, the bridge-free clause and
  `noWalkAbsorb_walkKeep_alpha_of_sideFaces`.  Clause 3 is copied.  The four local step clauses
  come from `noWalkAbsorb_step_of_closed` and `noWalkAbsorb_unique_of_closed`, since `G₁` and `G₂`
  are closed (`noWalkAbsorb_closed_of_sideFaces`, `noWalkAbsorb_mem_walk_of_first`/`_second`).
* `FourPieceWitness.noWalkAbsorb_of_noPlanarDegenStep`: the converse, through the right
  disjunct.

## LOUD: the two statements are EQUIVALENT, and the LEFT disjunct is dead

Together the two theorems show `NoWalkAbsorbStatement ↔ NoPlanarDegenStepStatement`.
`NoWalkAbsorbAudit.lean` (`noWalkAbsorb_left_false`) shows that LEFT fails as soon as `a` has a
contact dart `d` on `Π_i` with `faceOf d ∉ sideFaces K.walk`, `d ∉ G₁` and `d ∉ G₂`.  That is
the generic nondegenerate situation, since `S.nondegenerate` makes every contact arc nonempty.
The outer walk of the whole pocket then runs along the contact of `a`, with an `a.1` face
across.  So on every instance that matters, a proof of `NoWalkAbsorbStatement` must prove the
right disjunct, which is the target conclusion.  The residual is **not** strictly smaller in
proof content there.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

/-- **The target from the whole-pocket residual.**  See the module docstring. -/
theorem noPlanarDegenStep_of_noWalkAbsorb (h : NoWalkAbsorbStatement.{u, w, v}) :
    NoPlanarDegenStepStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbj hdisj hlet hW hK1 hK2 G₁ hG₁ G₂ hG₂ hw
    hout hinE houtE C hC hCf hCa hCb hno hnc
  rcases h D eps X a b K hij hai hbj hdisj hlet hW hK1 hK2 G₁ hG₁ G₂ hG₂ hw hout hinE houtE C hC
      hCf hCa hCb hno hnc with hL | hR
  · obtain ⟨ow, E, hbr, hdarts, h1, h2, h3, h4⟩ := hL
    have hcl₁ : ∀ g ∈ G₁.darts, g ∈ ow → X.toCombMap.facePerm g ∈ G₁.darts →
        X.toCombMap.facePerm g ∈ ow :=
      noWalkAbsorb_closed_of_sideFaces E G₁.darts
        (fun x hx => noWalkAbsorb_mem_walk_of_first K hG₁ hx)
    have hcl₂ : ∀ g ∈ G₂.darts, g ∈ ow → X.toCombMap.facePerm g ∈ G₂.darts →
        X.toCombMap.facePerm g ∈ ow :=
      noWalkAbsorb_closed_of_sideFaces E G₂.darts
        (fun x hx => noWalkAbsorb_mem_walk_of_second K hG₂ hx)
    refine Or.inl ⟨sideFaces X.toCombMap K.walk, ow, E, hCf, Finset.Subset.refl _, ?_, h1, h2,
      h3, h4, fun hoff => noWalkAbsorb_step_of_closed E i G₁ hcl₁ hoff,
      fun hall => noWalkAbsorb_unique_of_closed E i G₁ hcl₁ hall,
      fun hoff => noWalkAbsorb_step_of_closed E j G₂ hcl₂ hoff,
      fun hall => noWalkAbsorb_unique_of_closed E j G₂ hcl₂ hall⟩
    intro d hd
    rcases hdarts d hd with hg | hg | ⟨hna, hnb⟩
    · refine Or.inl ((Embedded.mem_invDarts_iff _ _).mpr ?_)
      rw [X.toCombMap.alpha_involutive d]
      exact hg
    · refine Or.inr (Or.inl ((Embedded.mem_invDarts_iff _ _).mpr ?_))
      rw [X.toCombMap.alpha_involutive d]
      exact hg
    · exact Or.inr (Or.inr ⟨hbr d hd, hna, hnb,
        Or.inl (noWalkAbsorb_walkKeep_alpha_of_sideFaces E hd (hbr d hd))⟩)
  · exact hR

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.noPlanarDegenStep_of_noWalkAbsorb

/-- **The converse.**  The target gives the residual through its right disjunct, so the two
statements are equivalent. -/
theorem noWalkAbsorb_of_noPlanarDegenStep (h : NoPlanarDegenStepStatement.{u, w, v}) :
    NoWalkAbsorbStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbj hdisj hlet hW hK1 hK2 G₁ hG₁ G₂ hG₂ hw
    hout hinE houtE C hC hCf hCa hCb hno hnc
  exact Or.inr (h D eps X a b K hij hai hbj hdisj hlet hW hK1 hK2 G₁ hG₁ G₂ hG₂ hw hout hinE
    houtE C hC hCf hCa hCb hno hnc)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.noWalkAbsorb_of_noPlanarDegenStep

/-- **The residual and the target are equivalent.** -/
theorem noWalkAbsorb_iff_noPlanarDegenStep :
    NoWalkAbsorbStatement.{u, w, v} ↔ NoPlanarDegenStepStatement.{u, w, v} :=
  ⟨noPlanarDegenStep_of_noWalkAbsorb, noWalkAbsorb_of_noPlanarDegenStep⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.noWalkAbsorb_iff_noPlanarDegenStep

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
