import GroupApproximation.Steinberg.FreePropertyT
import GroupApproximation.Steinberg.Functoriality

/-!
# Finite root control in every finite Steinberg rank

The analytic estimate is genuinely rank three, but every ordered root in
`St_n` lies in an embedded rank-three Steinberg subgroup.  Restricting a
representation along that embedding transports the rank-three estimate to
the chosen root.  Consequently the finite set consisting of the unit and
free-algebra generators in every ordered root controls the entire root union
in every rank at least three.

This is the finite-control half of the higher-rank property-`(T)` argument.
It deliberately does not assert that the higher-rank root union is a Kazhdan
subset; that is the remaining strong-grading/magic-graph input.
-/

namespace GroupApproximation
namespace SteinbergHigherRankFiniteControl

open SteinbergGroup
open SteinbergFreePropertyT
open SteinbergRootPlaneFourier

noncomputable section

variable (X : Type*) [Fintype X]

/-- Ordered distinct pairs in an arbitrary index type. -/
abbrev IndexedRoot (I : Type*) := {p : I × I // p.1 ≠ p.2}

/-- One unit-or-generator control in a specified ordered root. -/
def finiteControlElementAt (n : ℕ)
    (p : IndexedRoot (Fin n) × Option (Fin (Fintype.card X))) :
    SteinbergGroup (Fin n) (SteinbergRootPlaneFourier.FreeRing X) :=
  SteinbergGroup.x p.1.1.1 p.1.1.2 p.1.2
    (SteinbergGroup.finiteControlCoefficient X p.2)

/-- Unit and free-generator coefficients in every ordered root of `St_n`. -/
def finiteControlSetAt (n : ℕ) :
    Finset (SteinbergGroup (Fin n)
      (SteinbergRootPlaneFourier.FreeRing X)) := by
  classical
  exact (Finset.univ : Finset
    (IndexedRoot (Fin n) × Option (Fin (Fintype.card X)))).image
      (finiteControlElementAt X n)

theorem finiteControlElementAt_mem (n : ℕ)
    (p : IndexedRoot (Fin n) × Option (Fin (Fintype.card X))) :
    finiteControlElementAt X n p ∈ finiteControlSetAt X n := by
  classical
  exact Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩

/-- The embedding of a chosen ordered triple into `Fin n`. -/
def tripleEmbedding {n : ℕ} (i j k : Fin n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : Fin 3 ↪ Fin n where
  toFun := ![i, j, k]
  inj' := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all

@[simp] theorem tripleEmbedding_zero {n : ℕ} (i j k : Fin n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    tripleEmbedding i j k hij hik hjk 0 = i := rfl

@[simp] theorem tripleEmbedding_one {n : ℕ} (i j k : Fin n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    tripleEmbedding i j k hij hik hjk 1 = j := rfl

@[simp] theorem tripleEmbedding_two {n : ℕ} (i j k : Fin n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    tripleEmbedding i j k hij hik hjk 2 = k := rfl

/-- A rank-three finite control maps to the corresponding higher-rank
finite control. -/
theorem indexMap_finiteControlElement {n : ℕ} (e : Fin 3 ↪ Fin n)
    (p : A2Root × Option (Fin (Fintype.card X))) :
    SteinbergGroup.indexMap e (SteinbergGroup.finiteControlElement X p) =
      finiteControlElementAt X n
        (⟨(e p.1.1.1, e p.1.1.2), e.injective.ne p.1.2⟩, p.2) := by
  simp [SteinbergGroup.finiteControlElement, finiteControlElementAt]

/-- The global finite controls bound displacement by every root element in
every rank at least three. -/
theorem finiteControlSetAt_controls_rootSet (n : ℕ) (hn : 3 ≤ n) :
    ControlsSubsetDisplacement
      (SteinbergGroup (Fin n) (SteinbergRootPlaneFourier.FreeRing X))
      (finiteControlSetAt X n)
      (SteinbergGroup.rootSet (I := Fin n)
        (R := SteinbergRootPlaneFourier.FreeRing X))
      (12 * Fintype.card X + 13 : ℝ) := by
  classical
  intro E _ _ _ rho z hz δ hδ hnear g hg
  rcases hg with ⟨i, k, hik, hg⟩
  obtain ⟨a, rfl⟩ := hg
  obtain ⟨j, hji, hjk⟩ :=
    Fin.exists_ne_and_ne_of_two_lt i k (by omega)
  have hij : i ≠ j := hji.symm
  let e : Fin 3 ↪ Fin n := tripleEmbedding i j k hij hik hjk
  let rho3 : SteinbergGroup (Fin 3)
      (SteinbergRootPlaneFourier.FreeRing X) →* (E ≃ₗᵢ[ℝ] E) :=
    rho.comp (SteinbergGroup.indexMap e)
  have hnear3 : ∀ s ∈ SteinbergGroup.finiteControlSet X,
      ‖rho3 s z - z‖ < δ := by
    intro s hs
    rcases Finset.mem_image.mp hs with ⟨p, -, rfl⟩
    change ‖rho (SteinbergGroup.indexMap e
      (SteinbergGroup.finiteControlElement X p)) z - z‖ < δ
    rw [indexMap_finiteControlElement X e p]
    exact hnear _ (finiteControlElementAt_mem X n _)
  have hg3 : SteinbergGroup.x (0 : Fin 3) 2 (by decide) a ∈
      (SteinbergGroup.a2System
        (R := SteinbergRootPlaneFourier.FreeRing X)).rootSet := by
    exact ⟨0, 2, by decide, ⟨a, rfl⟩⟩
  have hmove := finiteControlSet_controls_rootSet X
    E rho3 z hz δ hδ hnear3
    (SteinbergGroup.x (0 : Fin 3) 2 (by decide) a) hg3
  simpa [rho3, e] using hmove

end
end SteinbergHigherRankFiniteControl
end GroupApproximation
