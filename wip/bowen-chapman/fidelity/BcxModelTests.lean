/-
Model tests for the definitions in the Bowen–Chapman Palomar shared block.
Fidelity driver, unwired: no lake target builds files under wip/.  Compiled
green on MSI on 2026-09-12, 21:28-21:31 CDT, against the origin/main bytes of
d71ae9349.

Build:
  lake build PalomarBowenChapmanSolution
  lake env lean <path>/BcxModelTests.lean

Every statement below is phrased in the CHALLENGE vocabulary
(`BowenChapman.IsSoficGroup`, `BowenChapman.IsSurjunctive`,
`BowenChapman.cellularAutomaton`), which is what the Comparator compares.
The development's own positive controls live in the `GroupApproximation`
vocabulary and therefore do not, by themselves, calibrate the challenge.
-/
import Palomar.BowenChapmanSolution
import GroupApproximation.Sofic.SoficPositiveControl
import GroupApproximation.Sofic.FreeGroupResiduallyFinite
import GroupApproximation.Sofic.HyperlinearReduction
import GroupApproximation.Dynamics.SurjunctivityTransfer

namespace BowenChapman

open GroupApproximation

/-! ## Positive controls: `IsSoficGroup` is satisfied, not merely refutable -/

/-- Finite groups. -/
theorem test_isSoficGroup_of_finite (G : Type) [Group G] [Finite G] :
    IsSoficGroup G :=
  isSoficGroup_of_isSofic (isSofic_of_finite G)

/-- The infinite cyclic group. -/
theorem test_isSoficGroup_int : IsSoficGroup (Multiplicative ℤ) :=
  isSoficGroup_of_isSofic isSofic_multiplicative_int

/-- A nonabelian free group: the ambient group of Bowen–Chapman's own setting. -/
theorem test_isSoficGroup_freeGroup : IsSoficGroup (FreeGroup Bool) :=
  isSoficGroup_of_isSofic (isSofic_freeGroup Bool)

/-- Every residually finite group. -/
theorem test_isSoficGroup_of_residuallyFinite (G : Type) [Group G]
    [Group.ResiduallyFinite G] : IsSoficGroup G :=
  isSoficGroup_of_isSofic isSofic_of_residuallyFinite

/-! ## Positive controls: `IsSurjunctive` is satisfied -/

/-- Finite groups, proved directly from the challenge's definition and nothing
else: a full shift over a finite group and a finite palette is finite, and an
injective self-map of a finite type is onto. -/
theorem test_isSurjunctive_of_finite (G : Type) [Group G] [Finite G] :
    IsSurjunctive G := by
  intro A hA n γ φ hinj
  haveI : Finite A := hA
  haveI : Finite (G → A) := inferInstance
  exact Finite.injective_iff_surjective.mp hinj

/-- A nonabelian free group. -/
theorem test_isSurjunctive_freeGroup : IsSurjunctive (FreeGroup Bool) :=
  isSurjunctive_of_surjunctive Surjunctivity.isSurjunctive_of_residuallyFinite

/-- Every residually finite group. -/
theorem test_isSurjunctive_of_residuallyFinite (G : Type) [Group G]
    [Group.ResiduallyFinite G] : IsSurjunctive G :=
  isSurjunctive_of_surjunctive Surjunctivity.isSurjunctive_of_residuallyFinite

/-! ## Negative control: the palette's finiteness is load-bearing

If `[Finite A]` were dropped from `IsSurjunctive`, the predicate would be false
for every group.  So the definition is not satisfied for a degenerate reason. -/

theorem test_infinite_palette_breaks_surjunctivity :
    ∃ (A : Type) (n : ℕ) (γ : Fin n → Multiplicative ℤ) (φ : (Fin n → A) → A),
      Function.Injective (cellularAutomaton γ φ) ∧
        ¬ Function.Surjective (cellularAutomaton γ φ) := by
  refine ⟨ℕ, 1, fun _ => 1, fun v => v 0 + 1, ?_, ?_⟩
  · intro c d h
    funext x
    have hx := congrFun h x
    simp only [cellularAutomaton, mul_one, add_left_inj] at hx
    exact hx
  · intro hsurj
    obtain ⟨c, hc⟩ := hsurj (fun _ => 0)
    have hx := congrFun hc 1
    simp only [cellularAutomaton, mul_one] at hx
    omega

/-! ## Degeneracy checks inside `IsSoficGroup` -/

/-- The separation clause has content: below `ε = 1` it forces the model to
distinguish distinct elements of the test set, hence forces `2 ≤ card Y`. -/
theorem test_separation_is_not_vacuous (Y : FiniteCarrier) (p q : Equiv.Perm Y)
    (ε : ℝ) (hε : ε < 1) (h : 1 - ε ≤ hammingDist Y p q) : p ≠ q := by
  intro hpq
  rw [hpq] at h
  have hzero : hammingDist Y q q = 0 := by
    simp [hammingDist]
  rw [hzero] at h
  linarith

/-- Pestov's condition (2) (`d(σ(1), Id) ≤ ε`) is implied by the
multiplicativity clause at `g = h = 1`, so dropping it from the shared block
loses nothing. -/
theorem test_identity_clause_is_implied (Y : FiniteCarrier) (p : Equiv.Perm Y)
    (ε : ℝ) (h : hammingDist Y p (p * p) ≤ ε) : hammingDist Y 1 p ≤ ε := by
  have key : hammingDist Y (p * 1) (p * p) = hammingDist Y 1 p :=
    hammingDistance_left_invariant ⟨Y.carrier, Y.fintype, Y.decidableEq⟩ p 1 p
  rw [mul_one] at key
  rw [← key]
  exact h

/-! ## The finite-generation clause is Mathlib's `Group.FG`, unfolded -/

theorem test_fg_clause_iff (G : Type) [Group G] :
    (∃ S : Finset G, Subgroup.closure (S : Set G) = ⊤) ↔ Group.FG G :=
  ⟨fun h => ⟨h⟩, fun h => h.out⟩

/-! ## `cellularAutomaton` reproduces the identity and a constant rule -/

/-- Memory `(1)` with the projection rule is the identity, so the class of
automata the definition quantifies over is nonempty and contains bijections. -/
theorem test_cellularAutomaton_id {G : Type} [Group G] {A : Type} :
    cellularAutomaton (G := G) (A := A) (fun _ : Fin 1 => 1) (fun v => v 0) = id := by
  funext c x
  simp [cellularAutomaton]

end BowenChapman

#print axioms BowenChapman.not_all_surjunctive_groups_sofic
#print axioms BowenChapman.exists_finitelyGenerated_surjunctive_not_sofic
