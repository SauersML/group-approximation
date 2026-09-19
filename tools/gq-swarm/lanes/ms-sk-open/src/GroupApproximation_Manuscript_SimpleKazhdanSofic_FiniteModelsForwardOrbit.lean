import GroupApproximation.Manuscript.SimpleKazhdanSofic.MinimalSubshiftPeriodicWord
import GroupApproximation.Meta.AxiomGuard

/-!
# Forward orbits of a minimal subshift are dense

`simple_kazhdan_sofic_group.tex` at 9047d0d3c, "Finite models", tex 135–137:

> Fix $x\in X$ and $\ell\ge0$. By minimality the forward orbit of $x$ is dense, so every word of
> $X$ occurs in $x_{[0,\infty)}$, and $x_{[0,2\ell)}$ recurs at arbitrarily large positions.

* `subset_closure_forwardOrbit_of_minimal`: the forward orbit `{T^n x : n ≥ 0}` is dense in `X`.  A
  basic neighbourhood of `y ∈ X` fixes finitely many coordinates inside `[-r, r]`; by uniform
  recurrence the word `y_{[-r, r]}` occurs in `x` at a position at least `r`, and the corresponding
  forward translate of `x` agrees with `y` on `[-r, r]`.
* `exists_nat_word_eq_of_minimal` (every word occurs in `x_{[0,∞)}`) and
  `exists_recurrence_of_minimal` (recurrence at arbitrarily large positions) are in
  `MinimalSubshiftPeriodicWord`.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic

open SymbolicDynamics.FullShift WordGraph

variable {A : Type*}

/-- **By minimality the forward orbit of `x` is dense** (tex 135–136). -/
theorem subset_closure_forwardOrbit_of_minimal [TopologicalSpace A] [DiscreteTopology A] [Finite A]
    {X : Set (ℤ → A)} (hXc : IsClosed X) (hX : ∀ m : ℤ, Set.MapsTo (shift m) X X)
    (hmin : ∀ C : Set (ℤ → A), IsClosed C → C ⊆ X → (∀ g : ℤ, Set.MapsTo (shift g) C C) →
      C = ∅ ∨ C = X) {x : ℤ → A} (hx : x ∈ X) :
    X ⊆ closure (Set.range fun n : ℕ => shift (n : ℤ) x) := by
  intro y hy
  refine mem_closure_iff.2 fun U hU hyU => ?_
  obtain ⟨I, u, hu, hIu⟩ := isOpen_pi_iff.mp hU y hyU
  obtain ⟨r, hr⟩ : ∃ r : ℕ, r = I.sup Int.natAbs := ⟨_, rfl⟩
  obtain ⟨ℓ, hℓ⟩ := isUniformlyRecurrentAt_of_minimal hXc hX hmin (2 * r + 1)
  obtain ⟨j, -, hjw⟩ := hℓ x hx (r : ℤ) (word y (-(r : ℤ)) (2 * r + 1)) (word_mem_language hX hy _ _)
  refine ⟨shift ((2 * r + j : ℕ) : ℤ) x, hIu (Set.mem_pi.2 fun a ha => ?_), ⟨2 * r + j, rfl⟩⟩
  have har : a.natAbs ≤ r := by
    rw [hr]
    exact Finset.le_sup (f := Int.natAbs) ha
  obtain ⟨t, ht⟩ : ∃ t : ℕ, (t : ℤ) = r + a := ⟨(r + a).toNat, Int.toNat_of_nonneg (by omega)⟩
  have h := congrFun hjw ⟨t, by omega⟩
  simp only [word_apply] at h
  rw [shift_apply, show (((2 * r + j : ℕ) : ℤ) + a) = (r : ℤ) + j + t by push_cast; omega, h,
    show -(r : ℤ) + t = a by omega]
  exact (hu a ha).2

end SimpleKazhdanSofic
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.SimpleKazhdanSofic.subset_closure_forwardOrbit_of_minimal
