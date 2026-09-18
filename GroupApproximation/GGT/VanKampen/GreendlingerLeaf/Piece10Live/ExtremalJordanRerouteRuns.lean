import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalJordanRerouteLoop
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalArcEndExists
import GroupApproximation.Meta.AxiomGuard

/-!
# One removed run up to loop darts gives linked runs

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-30.

`ExtremalJordanRerouteLoopRun K r`: the pocket walk splits as `A ++ B ++ C` with either

* every dart of `B` removed and every dart of `A ++ C` kept or a loop, or
* every dart of `A ++ C` removed and every dart of `B` kept or a loop.

This extends `ExtremalArcEndExistsOneRun` (lane gl-p10-25) by allowing loop darts
(`vertexOf x = vertexOf (alpha x)`) on the kept side.  The main result is
`extremalJordanReroute_linked_of_loopRun`: such a class has linked runs (the linear
`ExtremalMinimalLinkedRuns`).

## Proof

Take a removed gap `B0` between kept darts `d`, `e` of the walk.

* If every dart of `B0` is a loop, the walk chain through `d, B0, e` links it
  (`extremalJordanReroute_chain_loops`).
* First alternative, some `b ∈ B0` not a loop: `b` lies in `B`.  A removed non-loop dart of
  `A0` or `C0` would also lie in `B`, and the nodup segment lemma would then put `d` or `e` in
  `B`, but they are kept.  So `A0` and `C0` are kept-or-loop, and the loop parity count
  `extremalJordanReroute_closed_run_loops` applies.
* Second alternative: `d` and `e` are kept, so they lie in `B`.  By the segment lemma `B0 ⊆ B`,
  so its darts are kept-or-loop, and being removed they are loops: the chain case.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove

section RerouteRuns

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **One removed run up to loops**: the pocket walk splits as `A ++ B ++ C` with `B` removed and
`A ++ C` kept or loops, or with `A ++ C` removed and `B` kept or loops. -/
def ExtremalJordanRerouteLoopRun (K : PocketFaceSet D eps X lo hi) (r : X.toCombMap.Dart) :
    Prop :=
  ∃ A B C : List X.toCombMap.Dart, K.boundary.cycle = A ++ B ++ C ∧
    (((∀ x ∈ A ++ C, P10ExtremalResidual.keptPred K r x = true ∨
          X.toCombMap.vertexOf x = X.toCombMap.vertexOf (X.toCombMap.alpha x)) ∧
        ∀ x ∈ B, P10ExtremalResidual.keptPred K r x = false) ∨
      ((∀ x ∈ A ++ C, P10ExtremalResidual.keptPred K r x = false) ∧
        ∀ x ∈ B, P10ExtremalResidual.keptPred K r x = true ∨
          X.toCombMap.vertexOf x = X.toCombMap.vertexOf (X.toCombMap.alpha x)))

/-- **A lone removed run on the pocket walk is linked, with loops allowed outside it.** -/
theorem extremalJordanReroute_closed_run_pocket (K : PocketFaceSet D eps X lo hi)
    (hK : K.ClosedWalk) (r : X.toCombMap.Dart) {A B C : List X.toCombMap.Dart}
    {d e : X.toCombMap.Dart} (hdec : K.boundary.cycle = A ++ d :: (B ++ e :: C))
    (hA : ∀ x ∈ A, P10ExtremalResidual.keptPred K r x = true ∨
      X.toCombMap.vertexOf x = X.toCombMap.vertexOf (X.toCombMap.alpha x))
    (hd : P10ExtremalResidual.keptPred K r d = true)
    (hB : ∀ x ∈ B, P10ExtremalResidual.keptPred K r x = false)
    (he : P10ExtremalResidual.keptPred K r e = true)
    (hC : ∀ x ∈ C, P10ExtremalResidual.keptPred K r x = true ∨
      X.toCombMap.vertexOf x = X.toCombMap.vertexOf (X.toCombMap.alpha x)) :
    X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e :=
  extremalJordanReroute_closed_run_loops X.toCombMap K.boundary.cycle_mem_iff
    K.boundary.cycle_nodup hK.1 (regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r)
    (regionColour_step X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r)
    (regionColour_indep K.boundary.cycle_mem_iff r) hdec hA hd hB he hC

/-- **A gap of loop darts on the pocket walk is linked.** -/
theorem extremalJordanReroute_loops_pocket (K : PocketFaceSet D eps X lo hi)
    (hK : K.ClosedWalk) {A B C : List X.toCombMap.Dart} {d e : X.toCombMap.Dart}
    (hdec : K.boundary.cycle = A ++ d :: (B ++ e :: C))
    (hB : ∀ x ∈ B, X.toCombMap.vertexOf x = X.toCombMap.vertexOf (X.toCombMap.alpha x)) :
    X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e := by
  have hch : (d :: (B ++ [e])).IsChain
      fun a b => X.toCombMap.vertexOf (X.toCombMap.alpha a) = X.toCombMap.vertexOf b :=
    hK.1.infix ⟨A, C, by
      rw [hdec]
      simp⟩
  exact extremalJordanReroute_chain_loops X.toCombMap e B d hch hB

/-- **A class with one removed run up to loops has linked runs.** -/
theorem extremalJordanReroute_linked_of_loopRun (K : PocketFaceSet D eps X lo hi)
    (hK : K.ClosedWalk) (r : X.toCombMap.Dart) (h : ExtremalJordanRerouteLoopRun K r) :
    ExtremalMinimalLinkedRuns K r := by
  obtain ⟨A, B, C, hdec, ⟨hAC, hB⟩ | ⟨hAC, hB⟩⟩ := h
  · have hnd : (A ++ B ++ C).Nodup := by
      rw [← hdec]
      exact K.boundary.cycle_nodup
    have hrem : ∀ x ∈ A ++ B ++ C, P10ExtremalResidual.keptPred K r x = false →
        ¬X.toCombMap.vertexOf x = X.toCombMap.vertexOf (X.toCombMap.alpha x) → x ∈ B := by
      intro x hx hxk hxl
      rcases List.mem_append.mp hx with hx | hx
      · rcases List.mem_append.mp hx with hx | hx
        · rcases hAC x (List.mem_append_left C hx) with h1 | h1
          · exact absurd (h1.symm.trans hxk) (by decide)
          · exact absurd h1 hxl
        · exact hx
      · rcases hAC x (List.mem_append_right A hx) with h1 | h1
        · exact absurd (h1.symm.trans hxk) (by decide)
        · exact absurd h1 hxl
    intro A0 d B0 e C0 hdec0 hd he hB0 _
    by_cases hall : ∀ x ∈ B0,
        X.toCombMap.vertexOf x = X.toCombMap.vertexOf (X.toCombMap.alpha x)
    · exact extremalJordanReroute_loops_pocket K hK hdec0 hall
    push_neg at hall
    obtain ⟨b, hbB0, hbl⟩ := hall
    have hbB : b ∈ B := hrem b (by
      rw [← hdec, hdec0]
      simp [hbB0]) (hB0 b hbB0) hbl
    obtain ⟨B1, B2, rfl⟩ := List.append_of_mem hbB0
    refine extremalJordanReroute_closed_run_pocket K hK r hdec0 ?_ hd hB0 he ?_
    · intro x hx
      cases hxk : P10ExtremalResidual.keptPred K r x with
      | true => exact Or.inl rfl
      | false =>
        by_cases hxl : X.toCombMap.vertexOf x = X.toCombMap.vertexOf (X.toCombMap.alpha x)
        · exact Or.inr hxl
        · exfalso
          have hxB : x ∈ B := hrem x (by
            rw [← hdec, hdec0]
            simp [hx]) hxk hxl
          obtain ⟨A1, A2, rfl⟩ := List.append_of_mem hx
          have hseg := extremalMinimal_mem_segment_of_nodup hnd
            (show A ++ B ++ C = A1 ++ x :: ((A2 ++ d :: B1) ++ b :: (B2 ++ e :: C0)) by
              rw [← hdec, hdec0]
              simp) hxB hbB
          exact absurd (hd.symm.trans (hB d (hseg d (by simp)))) (by decide)
    · intro x hx
      cases hxk : P10ExtremalResidual.keptPred K r x with
      | true => exact Or.inl rfl
      | false =>
        by_cases hxl : X.toCombMap.vertexOf x = X.toCombMap.vertexOf (X.toCombMap.alpha x)
        · exact Or.inr hxl
        · exfalso
          have hxB : x ∈ B := hrem x (by
            rw [← hdec, hdec0]
            simp [hx]) hxk hxl
          obtain ⟨C1, C2, rfl⟩ := List.append_of_mem hx
          have hseg := extremalMinimal_mem_segment_of_nodup hnd
            (show A ++ B ++ C = (A0 ++ d :: B1) ++ b :: ((B2 ++ e :: C1) ++ x :: C2) by
              rw [← hdec, hdec0]
              simp) hbB hxB
          exact absurd (he.symm.trans (hB e (hseg e (by simp)))) (by decide)
  · have hnd : (A ++ B ++ C).Nodup := by
      rw [← hdec]
      exact K.boundary.cycle_nodup
    have hkeptB : ∀ x ∈ A ++ B ++ C, P10ExtremalResidual.keptPred K r x = true → x ∈ B := by
      intro x hx hxk
      rcases List.mem_append.mp hx with hx | hx
      · rcases List.mem_append.mp hx with hx | hx
        · exact absurd ((hAC x (List.mem_append_left C hx)).symm.trans hxk) (by decide)
        · exact hx
      · exact absurd ((hAC x (List.mem_append_right A hx)).symm.trans hxk) (by decide)
    intro A0 d B0 e C0 hdec0 hd he hB0 _
    have hdB : d ∈ B := hkeptB d (by
      rw [← hdec, hdec0]
      simp) hd
    have heB : e ∈ B := hkeptB e (by
      rw [← hdec, hdec0]
      simp) he
    have hseg := extremalMinimal_mem_segment_of_nodup hnd (hdec.symm.trans hdec0) hdB heB
    refine extremalJordanReroute_loops_pocket K hK hdec0 ?_
    intro x hx
    rcases hB x (hseg x hx) with h1 | h1
    · exact absurd (h1.symm.trans (hB0 x hx)) (by decide)
    · exact h1

end RerouteRuns

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.ExtremalJordanRerouteLoopRun
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanReroute_closed_run_pocket
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanReroute_loops_pocket
