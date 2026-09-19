/-
The challenge's `IsSurjunctive` is not weaker than topological surjunctivity.
Built by the PalomarSurjunctiveNonsoficModelTests target and Palomar CI.
The original versions were checked on MSI on September 12, 2026; this
renamed integration has not been recompiled during the present pass.

`Palomar/SurjunctiveNonsoficSolution.lean` proves `Surjunctivity.IsSurjunctive G →
IsSurjunctive G`, which is the direction the theorem needs.  The converse below
shows the two are equivalent, so the challenge's surjunctivity hypothesis is
not a weakened one: Curtis–Hedlund–Lyndon (`isFiniteMemory_of_continuous_equivariant`)
turns a continuous equivariant map of a finite full shift into a memory-set
automaton, and a `Finset` memory set enumerates as a finite tuple.
-/
import Palomar.SurjunctiveNonsoficSolution

namespace SurjunctiveNonsofic

open GroupApproximation

/-- A memory-set automaton is a finite-list automaton, after enumerating the
memory set. -/
theorem localMap_eq_cellularAutomaton {G : Type} [Group G] {B : Type}
    (M : Finset G) (μ : (M → B) → B) :
    Surjunctivity.localMap M μ
      = cellularAutomaton (fun i : Fin M.card => ((M.equivFin.symm i : M) : G))
          (fun v : Fin M.card → B => μ (fun m => v (M.equivFin m))) := by
  funext x g
  simp [cellularAutomaton, Surjunctivity.localMap]

/-- **The challenge's surjunctivity implies the development's.** -/
theorem surjunctive_of_isSurjunctive {G : Type} [Group G] (h : IsSurjunctive G) :
    Surjunctivity.IsSurjunctive G := by
  classical
  intro B hBfin hBtop hBdisc τ hc he hinj
  cases isEmpty_or_nonempty B with
  | inl hB =>
      haveI : IsEmpty (G → B) := ⟨fun f => hB.false (f 1)⟩
      exact fun y => isEmptyElim y
  | inr hB =>
      obtain ⟨M, hM⟩ := Surjunctivity.isFiniteMemory_of_continuous_equivariant hc he
      let b : B := Classical.arbitrary B
      let μ : (M → B) → B := fun v =>
        τ (fun g => if hg : g ∈ M then v ⟨g, hg⟩ else b) 1
      have hτ : τ = Surjunctivity.localMap M μ := by
        funext x g
        have h1 : τ (Surjunctivity.shift g x) 1 = τ x g := by
          have := congrFun (he g x) 1
          simpa [Surjunctivity.shift] using this
        have h2 : τ (Surjunctivity.shift g x) 1
            = τ (fun k => if hk : k ∈ M then x (g * k) else b) 1 := by
          refine hM _ _ 1 ?_
          intro m hm
          simp only [Surjunctivity.shift_apply, one_mul, dif_pos hm]
        rw [← h1, h2]
        rfl
      haveI : Finite B := Finite.of_fintype B
      rw [hτ, localMap_eq_cellularAutomaton]
      rw [hτ, localMap_eq_cellularAutomaton] at hinj
      exact h B M.card _ _ hinj

/-- The two surjunctivity notions agree. -/
theorem isSurjunctive_iff_surjunctive {G : Type} [Group G] :
    IsSurjunctive G ↔ Surjunctivity.IsSurjunctive G :=
  ⟨surjunctive_of_isSurjunctive, isSurjunctive_of_surjunctive⟩

end SurjunctiveNonsofic
