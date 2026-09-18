import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.RigidSplitSupport
import GroupApproximation.Meta.AxiomGuard

/-!
# Group-theoretic definability of disjoint involution supports, part 1: the formula

Lane `sk-flip-23c`.  Census row `2e7c7d9ab149` (tex: "for topological full groups the converse
holds"; the row names no sentence of the current tex, so there is no tex line).

The formula `RubinInvolutionDisjointFormula f k` says: `[f, k] = 1`, and every `g` in the
centraliser of `P = f k` satisfies `[f, g f g⁻¹] = 1`.  It is first order in the group
language, so group isomorphisms preserve it (`rubinInvDisj_formula_map`).

This file proves the facts that need no dynamics.
* `rubinInvDisj_formula_of_disjoint`: homeomorphisms with disjoint moved sets satisfy the formula.
  Each of `f` and `f' = g f g⁻¹` acts at each point as the identity or as `P`, and both commute
  with `P` (`rubinInvDisj_commute_of_orbit`).
* `rubinInvDisj_not_commute_of_points` and `rubinInvDisj_not_commute_of_local`: pointwise
  witnesses of `[f, g f g⁻¹] ≠ 1`.  Part 2 uses them for the converse.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

variable {X : Type*} [TopologicalSpace X]

/-- `f` and `k` commute, and `f` commutes with each conjugate `g f g⁻¹` by an element `g` of
the centraliser of `f * k`. -/
def RubinInvolutionDisjointFormula {G : Type*} [Group G] (f k : G) : Prop :=
  f * k = k * f ∧ ∀ g : G, g * (f * k) = (f * k) * g → f * (g * f * g⁻¹) = (g * f * g⁻¹) * f

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.RubinInvolutionDisjointFormula

/-- Group isomorphisms preserve the formula. -/
theorem rubinInvDisj_formula_map {G H : Type*} [Group G] [Group H] (Φ : G ≃* H) {f k : G}
    (h : RubinInvolutionDisjointFormula f k) : RubinInvolutionDisjointFormula (Φ f) (Φ k) := by
  refine ⟨?_, fun g hg => ?_⟩
  · rw [← map_mul Φ f k, ← map_mul Φ k f, h.1]
  · have hg' : Φ.symm g * (f * k) = (f * k) * Φ.symm g := by
      apply Φ.injective
      simp only [map_mul, MulEquiv.apply_symm_apply]
      exact hg
    have h2 := congrArg Φ (h.2 _ hg')
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply] at h2
    exact h2

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.rubinInvDisj_formula_map

/-- Two homeomorphisms commuting with `P`, each acting at every point as the identity or as `P`,
commute. -/
theorem rubinInvDisj_commute_of_orbit {a b P : X ≃ₜ X} (haP : ∀ y, a (P y) = P (a y))
    (hbP : ∀ y, b (P y) = P (b y)) (ha : ∀ y, a y = y ∨ a y = P y)
    (hb : ∀ y, b y = y ∨ b y = P y) : a * b = b * a := by
  refine Homeomorph.ext fun y => ?_
  show a (b y) = b (a y)
  rcases hb y with h1 | h1 <;> rcases ha y with h2 | h2
  · rw [h1, h2, h1]
  · rw [h1, h2, hbP, h1]
  · rw [h1, h2, haP, h2, h1]
  · rw [h1, h2, haP, hbP, h1, h2]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.rubinInvDisj_commute_of_orbit

/-- Homeomorphisms with disjoint moved sets satisfy the formula (no involution hypothesis). -/
theorem rubinInvDisj_formula_of_disjoint {f k : X ≃ₜ X}
    (hd : Disjoint (movedSet f) (movedSet k)) :
    f * k = k * f ∧ ∀ g : X ≃ₜ X, g * (f * k) = (f * k) * g →
      f * (g * f * g⁻¹) = (g * f * g⁻¹) * f := by
  have hfk : f * k = k * f :=
    SupportedIn.commute_of_compl (supportedIn_iff_movedSet_subset.2 fun _ hy => hy)
      (supportedIn_iff_movedSet_subset.2 fun _ hy =>
        Set.mem_compl fun hyf => Set.disjoint_left.1 hd hyf hy)
  refine ⟨hfk, fun g hg => ?_⟩
  have hg' : ∀ w, g (f (k w)) = f (k (g w)) := fun w => DFunLike.congr_fun hg w
  have hgs : ∀ z, g.symm (f (k z)) = f (k (g.symm z)) := fun z => by
    apply g.injective
    rw [Homeomorph.apply_symm_apply, hg', Homeomorph.apply_symm_apply]
  have haP' : ∀ w, f (f (k w)) = f (k (f w)) := fun w =>
    congrArg f (DFunLike.congr_fun hfk w)
  have ha : ∀ y, f y = y ∨ f y = f (k y) := fun y => by
    by_cases hy : f y = y
    · exact Or.inl hy
    · right
      have hky : k y = y := by
        by_contra hky
        exact Set.disjoint_left.1 hd hy hky
      rw [hky]
  refine rubinInvDisj_commute_of_orbit (P := f * k) haP' ?_ ha ?_
  · intro y
    show g (f (g.symm (f (k y)))) = f (k (g (f (g.symm y))))
    rw [hgs, haP', hg']
  · intro y
    have e : g (g.symm y) = y := Homeomorph.apply_symm_apply g y
    rcases ha (g.symm y) with h | h
    · left
      show g (f (g.symm y)) = y
      rw [h, e]
    · right
      show g (f (g.symm y)) = f (k y)
      rw [h, hg', e]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.rubinInvDisj_formula_of_disjoint
