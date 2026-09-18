import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalTurnCut
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P06, cactus petal: cutting a walk at a repeated vertex (lane gl-p06-18)

Infrastructure for `P06LakeFree.PetalTurn.cellPocketLakeFreePetalTurn`
(`P06LakeFree/PetalTurnClose.lean`).  Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).

## Truth check

A walk `W₀ = u ++ y :: B ++ y' :: v` satisfying `PetalTurnInv` with `y` and `y'` at the same vertex
and NOT turning at both junctions `u | y` and `B | y'` is cut into the loop `y :: B` and the rest
`u ++ y' :: v`.  Both are shorter closed walks.  At a pinch vertex where the walk does turn at both
junctions the cut is not made (the outer piece could fail to be convex), matching the hypothesis.

## The mathematical proof

1. `invDarts W₀ = invDarts (y' :: v) ++ invDarts (y :: B) ++ invDarts u`, so both pieces reverse
   to sublists of `invDarts W₀ <+ T`.
2. The middle piece is convex (`runConvex_middle`); the outer piece is convex because the bad
   junction is not adjacent on the arcs (`runConvex_outer`, `not_adjacent_of_bad`).
3. The chain of `W₀` splits; the loop closes through `y'` and the rest joins through `y`, since
   `y` and `y'` share a vertex.
4. The side face of `W₀` is a side face of one piece (`side_split`).

## Manuscript status

Infrastructure for `thm:hull` (tex 2121); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalTurn

open Embedded SimpleClosedWalkSides

universe u w v

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **Cutting at a repeated vertex with a bad junction.** -/
theorem petalTurnInv_cut {X : DiscDiagram.{u, w, v} W} {T t₁ t₂ : List X.toCombMap.Dart}
    {x₀ : X.toCombMap.Dart} {u B v : List X.toCombMap.Dart} {y y' : X.toCombMap.Dart}
    (hE : PetalTurnEnv X T t₁ t₂) (hI : PetalTurnInv X T t₁ t₂ x₀ (u ++ y :: B ++ y' :: v))
    (hv : X.toCombMap.vertexOf y = X.toCombMap.vertexOf y')
    (hbad : ¬ ((∃ x ∈ u.getLast?, X.toCombMap.sigma (X.toCombMap.alpha x) = y) ∧
      (∃ x ∈ (y :: B).getLast?, X.toCombMap.sigma (X.toCombMap.alpha x) = y'))) :
    PetalTurnInv X T t₁ t₂ x₀ (y :: B) ∨ PetalTurnInv X T t₁ t₂ x₀ (u ++ y' :: v) := by
  have hL : invDarts X (u ++ y :: B ++ y' :: v) =
      invDarts X (y' :: v) ++ invDarts X (y :: B) ++ invDarts X u := by
    simp only [invDarts_append, List.append_assoc]
  have hsub : invDarts X (y' :: v) ++ invDarts X (y :: B) ++ invDarts X u <+ T := by
    rw [← hL]
    exact hI.sublist
  obtain ⟨hc₁, hc₂, hj₂⟩ := List.isChain_append.mp hI.chain
  obtain ⟨hcu, hcy, hj₁⟩ := List.isChain_append.mp hc₁
  -- the loop `y :: B`
  have hcl₁ : ∀ a ∈ (y :: B).getLast?, ∀ b ∈ (y :: B).head?,
      X.toCombMap.vertexOf (X.toCombMap.alpha a) = X.toCombMap.vertexOf b := by
    intro a ha b hb
    have hb' : some y = some b := hb
    rw [← Option.some.inj hb']
    have ha' : a ∈ (u ++ y :: B).getLast? := by
      rw [getLast?_append_cons]
      exact ha
    exact (hj₂ a ha' y' (Option.mem_def.mpr rfl)).trans hv.symm
  -- the rest `u ++ y' :: v`
  have hch₂ : (u ++ y' :: v).IsChain fun d e =>
      X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e := by
    refine List.IsChain.append hcu hc₂ ?_
    intro x hx z hz
    have hz' : some y' = some z := hz
    rw [← Option.some.inj hz']
    exact (hj₁ x hx y (Option.mem_def.mpr rfl)).trans hv
  have hcl₂ : ∀ a ∈ (u ++ y' :: v).getLast?, ∀ b ∈ (u ++ y' :: v).head?,
      X.toCombMap.vertexOf (X.toCombMap.alpha a) = X.toCombMap.vertexOf b := by
    intro a ha b hb
    rw [getLast?_append_cons] at ha
    have ha' : a ∈ (u ++ y :: B ++ y' :: v).getLast? := by
      rw [getLast?_append_cons]
      exact ha
    cases u with
    | nil =>
      have hb' : some y' = some b := hb
      rw [← Option.some.inj hb']
      exact (hI.closes a ha' y (Option.mem_def.mpr rfl)).trans hv
    | cons c us => exact hI.closes a ha' b hb
  have hsub₁ : invDarts X (y :: B) <+ T :=
    ((List.sublist_append_right (invDarts X (y' :: v)) (invDarts X (y :: B))).trans
      (List.sublist_append_left _ (invDarts X u))).trans hsub
  have hsub₂ : invDarts X (u ++ y' :: v) <+ T := by
    rw [invDarts_append]
    exact ((List.sublist_append_left (invDarts X (y' :: v)) (invDarts X (y :: B))).append
      (List.Sublist.refl (invDarts X u))).trans hsub
  have hconv₂₁ : OrderCactus.RunConvex (invDarts X (u ++ y' :: v)) t₁ := by
    rw [invDarts_append]
    exact runConvex_outer hE.nodup hI.sublist hE.infix₁ hI.conv₁ hL
      (not_adjacent_of_bad hE.chain₁ hbad)
  have hconv₂₂ : OrderCactus.RunConvex (invDarts X (u ++ y' :: v)) t₂ := by
    rw [invDarts_append]
    exact runConvex_outer hE.nodup hI.sublist hE.infix₂ hI.conv₂ hL
      (not_adjacent_of_bad hE.chain₂ hbad)
  have h₁ : ∀ d ∈ y :: B, d ∈ u ++ y :: B ++ y' :: v := fun d hd =>
    List.mem_append_left (y' :: v) (List.mem_append_right u hd)
  have h₂ : ∀ d ∈ u ++ y' :: v, d ∈ u ++ y :: B ++ y' :: v := by
    intro d hd
    rcases List.mem_append.mp hd with h | h
    · exact List.mem_append_left (y' :: v) (List.mem_append_left (y :: B) h)
    · exact List.mem_append_right (u ++ y :: B) h
  have hW : ∀ d ∈ u ++ y :: B ++ y' :: v, d ∈ y :: B ∨ d ∈ u ++ y' :: v := by
    intro d hd
    rcases List.mem_append.mp hd with h | h
    · rcases List.mem_append.mp h with h | h
      · exact Or.inr (List.mem_append_left (y' :: v) h)
      · exact Or.inl h
    · exact Or.inr (List.mem_append_right u h)
  rcases side_split h₁ h₂ hW hI.side with hs | hs
  · exact Or.inl
      { ne_nil := List.cons_ne_nil y B
        chain := hcy
        closes := hcl₁
        sublist := hsub₁
        conv₁ := runConvex_middle hE.nodup hI.sublist hE.infix₁ hI.conv₁ hL
        conv₂ := runConvex_middle hE.nodup hI.sublist hE.infix₂ hI.conv₂ hL
        side := hs }
  · exact Or.inr
      { ne_nil := List.append_ne_nil_of_right_ne_nil u (List.cons_ne_nil y' v)
        chain := hch₂
        closes := hcl₂
        sublist := hsub₂
        conv₁ := hconv₂₁
        conv₂ := hconv₂₂
        side := hs }

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalTurn.petalTurnInv_cut

/-- Both pieces of a cut are shorter. -/
theorem length_cut_lt {α : Type*} (u B v : List α) (y y' : α) :
    (y :: B).length < (u ++ y :: B ++ y' :: v).length ∧
      (u ++ y' :: v).length < (u ++ y :: B ++ y' :: v).length := by
  simp only [List.length_append, List.length_cons]
  omega

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalTurn.length_cut_lt

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalTurn
