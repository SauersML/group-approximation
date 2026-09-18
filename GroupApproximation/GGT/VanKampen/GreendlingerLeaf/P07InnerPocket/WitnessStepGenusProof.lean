import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepGenusStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepWindingProof
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-60: the pinched winding residual from a planar model

Lane gl-p07-60.  Certifies no printed sentence on its own.  NOT COMPILED.

* `witnessStepGenus_stepNext_of_model`: take a planar map `N` and a successor list `l'` on a face
  cycle `Γ`, and a word `w` with the order of `Γ` on `l'`.  Then every rotation step `(x, y)` of
  `l'.map ι` is a forward `StepNext` of `w`.
  * If `y'` follows `x'` in `Γ`, then `y` follows `x` in `w`.
  * Otherwise `Γ` rotates to `x' :: ((A₂ ++ D) ++ y' :: E)`.  The genus-zero first return
    (`witnessStepGenus_between_not_mem`) keeps `l'` out of `A₂ ++ D`.  An entry of `l` before
    `y` in `w` would come before `y'` in `Γ`, so it would lie in `D`.  Hence `y` is the first
    entry of `w` in `l`.
* `witnessStepGenus_pinched_of_bridge`: `WitnessStepWindingPinchedStatement` from
  `WitnessStepGenusBridgeStatement`, by `witnessStepDescent_bound_of_steps` (the first disjunct).
* `witnessStepGenus_skip_of_bridge`: the wire to `WitnessStepSkipStatement` through
  `witnessStepWinding_skip_of_pinched`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

/-- A rotation step of a mapped list lifts to a rotation step of the list. -/
theorem witnessStepGenus_rotate_lift {α β : Type*} (f : α → β) (l' : List α) {n : ℕ}
    {s t : List β} {x y : β} (h : (l'.map f).rotate n = s ++ x :: y :: t) :
    ∃ (s' t' : List α) (x' y' : α), l'.rotate n = s' ++ x' :: y' :: t' ∧ f x' = x ∧ f y' = y := by
  rw [← List.map_rotate] at h
  obtain ⟨l₁, l₂, h₁, -, h₃⟩ := List.map_eq_append_iff.mp h
  obtain ⟨x', r, rfl, hx, hr⟩ := List.map_eq_cons_iff.mp h₃
  obtain ⟨y', t', rfl, hy, -⟩ := List.map_eq_cons_iff.mp hr
  exact ⟨l₁, t', x', y', h₁, hx, hy⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepGenus_rotate_lift

/-- The two ends of a rotation step of a duplicate-free list are distinct. -/
theorem witnessStepGenus_ne_of_rotate {α : Type*} {l : List α} (hl : l.Nodup) {n : ℕ}
    {s t : List α} {x y : α} (h : l.rotate n = s ++ x :: y :: t) : x ≠ y := by
  have hnd : (s ++ x :: y :: t).Nodup := by
    rw [← h]
    exact List.nodup_rotate.mpr hl
  have h2 := (List.nodup_append.mp hnd).2.1
  intro hxy
  exact (List.nodup_cons.mp h2).1 (by rw [hxy]; exact List.mem_cons.mpr (Or.inl rfl))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepGenus_ne_of_rotate
