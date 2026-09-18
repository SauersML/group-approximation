import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# Trivial Hopf multiplier, stated over all free presentations

Lane `sk-rows-15` (carto-sk-rows, section 4): the group-theory half of Khanh (arXiv:2609.08428v1),
Theorem 5.4, namely the step `N₃ = [S₃, N₃]` of the rank-three kill.

Hopf's formula says `H₂(G) ≅ (R ∩ [F, F]) / [F, R]` for a free presentation `1 → R → F → G → 1`.
We do not use the formula (or its independence of the presentation).  Instead the vanishing of the
multiplier is *defined* by quantifying over every free presentation: for every surjection
`f : FreeGroup α →* G`, `ker f ∩ [F, F] ≤ [F, ker f]`.  This is the only form the five-term step
needs, and it implies nothing unproved.

The lane wrote the definition for `G : Type` and `α : Type`.  We state it universe-polymorphically
(`G α : Type u`), which is the lane's statement at `u = 0`.
-/

universe u

namespace GroupApproximation.SimpleKazhdanSofic.SkRows.HopfFiveTerm

/-- `G` has trivial Schur (Hopf) multiplier in presentation-free form: for every free
presentation `f : FreeGroup α ↠ G` with kernel `R`, one has `R ∩ [F, F] ≤ [F, R]`, i.e. the Hopf
quotient `(R ∩ [F, F]) / [F, R]` vanishes. -/
def HopfMultiplierTrivial (G : Type u) [Group G] : Prop :=
  ∀ (α : Type u) (f : FreeGroup α →* G), Function.Surjective f →
    f.ker ⊓ commutator (FreeGroup α) ≤ ⁅(⊤ : Subgroup (FreeGroup α)), f.ker⁆

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.HopfFiveTerm.HopfMultiplierTrivial

/-- Non-vacuity: the trivial group has trivial multiplier (then `R = F`). -/
theorem hopfMultiplierTrivial_of_subsingleton (G : Type u) [Group G] [Subsingleton G] :
    HopfMultiplierTrivial G := by
  intro α f _ x hx
  have hker : f.ker = ⊤ :=
    eq_top_iff.mpr fun y _ => MonoidHom.mem_ker.mpr (Subsingleton.elim _ _)
  rw [hker]
  exact (Subgroup.mem_inf.mp hx).2

#audit_axioms
  GroupApproximation.SimpleKazhdanSofic.SkRows.HopfFiveTerm.hopfMultiplierTrivial_of_subsingleton

end GroupApproximation.SimpleKazhdanSofic.SkRows.HopfFiveTerm
