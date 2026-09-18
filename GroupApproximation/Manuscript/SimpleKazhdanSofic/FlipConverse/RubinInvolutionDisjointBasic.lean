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
  f * k = k * f ∧
    ∀ g : G, g * (f * k) = (f * k) * g → f * (g * f * g⁻¹) = (g * f * g⁻¹) * f

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
        exact Set.disjoint_left.1 hd (show y ∈ movedSet f from hy)
          (show y ∈ movedSet k from hky)
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

/-- A pointwise witness of `[f, g f g⁻¹] ≠ 1` for an involution `f`: evaluate at `u = g a`. -/
theorem rubinInvDisj_not_commute_of_points {f g : X ≃ₜ X} (hff : ∀ z, f (f z) = z) {u a : X}
    (hga : g a = u) (hgfa : g (f a) = f a) (hgfu : g (f u) = f u) (hgu : g u ≠ a) :
    f * (g * f * g⁻¹) ≠ (g * f * g⁻¹) * f := by
  intro h
  have h1 : f (g (f (g.symm u))) = g (f (g.symm (f u))) := DFunLike.congr_fun h u
  have h2 : g.symm u = a := by rw [← hga, Homeomorph.symm_apply_apply]
  have h3 : g.symm (f u) = f u := by
    apply g.injective
    rw [Homeomorph.apply_symm_apply, hgfu]
  rw [h2, hgfa, hff, h3, hff] at h1
  exact hgu h1.symm

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.rubinInvDisj_not_commute_of_points

/-- The local witness: `h` supported in `W` with `h (h x) ≠ x`, `f W ∩ W = ∅`, and `q` fixing
`W` and `f W` pointwise.  Then `g = h q` does not make `f` commute with `g f g⁻¹`. -/
theorem rubinInvDisj_not_commute_of_local {f h q : X ≃ₜ X} (hff : ∀ z, f (f z) = z)
    {W : Set X} {x : X} (hxW : x ∈ W) (hh : SupportedIn h W) (hhx : h (h x) ≠ x)
    (hfW : ∀ w ∈ W, f w ∉ W) (hq : ∀ w ∈ W, q w = w ∧ q (f w) = f w) :
    f * ((h * q) * f * (h * q)⁻¹) ≠ ((h * q) * f * (h * q)⁻¹) * f := by
  have ha : h.symm x ∈ W := by
    by_contra ha
    have e : x = h.symm x := (Homeomorph.apply_symm_apply h x).symm.trans (hh _ ha)
    have e2 : h x = x := (congrArg h e).trans (Homeomorph.apply_symm_apply h x)
    exact hhx (by rw [e2, e2])
  have hq1 : q (h.symm x) = h.symm x := (hq _ ha).1
  have hq2 : q (f (h.symm x)) = f (h.symm x) := (hq _ ha).2
  have hq3 : q x = x := (hq _ hxW).1
  have hq4 : q (f x) = f x := (hq _ hxW).2
  have hfa : h (f (h.symm x)) = f (h.symm x) := hh _ (hfW _ ha)
  have hfx : h (f x) = f x := hh _ (hfW _ hxW)
  refine rubinInvDisj_not_commute_of_points hff (u := x) (a := h.symm x) ?_ ?_ ?_ ?_
  · show h (q (h.symm x)) = x
    rw [hq1, Homeomorph.apply_symm_apply]
  · show h (q (f (h.symm x))) = f (h.symm x)
    rw [hq2, hfa]
  · show h (q (f x)) = f x
    rw [hq4, hfx]
  · show h (q x) ≠ h.symm x
    rw [hq3]
    intro e
    apply hhx
    rw [e, Homeomorph.apply_symm_apply]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.rubinInvDisj_not_commute_of_local

end GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse
