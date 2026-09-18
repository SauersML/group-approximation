import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnGraded.CornerPotential
import GroupApproximation.Meta.AxiomGuard

/-!
# Graded Steinberg words in `K₂(C_2(𝔽₂))` are stably trivial (lane sk-lv-04)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`), leaf T1b.iii.  Let
`C = C_2(𝔽₂)` and let `m : Fin n → ℕ` be a potential.  Take `g ∈ K₂(n, C)` whose Steinberg word
uses only generators `x_{ij}(a)` with `a` `(m i, m j)`-admissible (`g ∈ skCohnGr_gradedSt m`).
Then `g` is stably trivial:

1. The potential corner map sends `g` to the image of some `y ∈ St_n(C₀)`
   (`skCohnGr_cornerMap_mem_range`).
2. After padding by two, that image equals `g` (`skCohnGr_indexMap_cornerMap_eq`).  Since
   `C₀ ⊆ C` is injective, the padded `y` lies in `K₂(C₀)`.
3. Stable `K₂(C₀) = 0` (`LVCohnColimit.skCohnLimK2_stableK2Trivial_degreeZero`) kills the
   padded `y`, and so the padded `g`.

The stably trivial elements of `St_n(R)` form a subgroup `skCohnGr_stablyTrivial R n`.  Hence
products of such graded `K₂` elements, possibly for different potentials, are stably trivial
(`skCohnGr_closure_gradedK2_le`).
-/

namespace GroupApproximation.Full.LVCohnGraded

open SteinbergGroup

noncomputable section

/-- The elements of `St_n(R)` that die after padding: the kernel of `St_n(R) → St(R)`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
def skCohnGr_stablyTrivial (R : Type*) [Ring R] (n : ℕ) :
    Subgroup (SteinbergGroup (Fin n) R) where
  carrier := {g | ∃ (N : ℕ) (h : n ≤ N), indexMap (Fin.castLEEmb h) g = 1}
  mul_mem' := by
    intro a b ha hb
    obtain ⟨N₁, h₁, ha⟩ := ha
    obtain ⟨N₂, h₂, hb⟩ := hb
    refine ⟨max N₁ N₂, h₁.trans (le_max_left N₁ N₂), ?_⟩
    have ea : indexMap (Fin.castLEEmb (h₁.trans (le_max_left N₁ N₂))) a = 1 := by
      have e := LVH2GL3.indexMap_castLEEmb_castLEEmb h₁ (le_max_left N₁ N₂) a
      rw [ha, map_one] at e
      exact e.symm
    have eb : indexMap (Fin.castLEEmb (h₁.trans (le_max_left N₁ N₂))) b = 1 := by
      have e := LVH2GL3.indexMap_castLEEmb_castLEEmb h₂ (le_max_right N₁ N₂) b
      rw [hb, map_one] at e
      exact e.symm
    rw [map_mul, ea, eb, mul_one]
  one_mem' := ⟨n, le_rfl, map_one _⟩
  inv_mem' := by
    intro a ha
    obtain ⟨N, h, ha⟩ := ha
    exact ⟨N, h, by rw [map_inv, ha, inv_one]⟩

#audit_axioms GroupApproximation.Full.LVCohnGraded.skCohnGr_stablyTrivial

/-- Membership in `skCohnGr_stablyTrivial`.  (`simple_kazhdan_sofic_group.tex` l.733-735,
leaf T1b.iii.) -/
theorem skCohnGr_mem_stablyTrivial {R : Type*} [Ring R] {n : ℕ}
    {g : SteinbergGroup (Fin n) R} :
    g ∈ skCohnGr_stablyTrivial R n ↔ ∃ (N : ℕ) (h : n ≤ N), indexMap (Fin.castLEEmb h) g = 1 :=
  Iff.rfl

#audit_axioms GroupApproximation.Full.LVCohnGraded.skCohnGr_mem_stablyTrivial

/-- **Graded vanishing** (`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii).  An element
of `K₂(n, C_2(𝔽₂))` whose Steinberg word is graded for some potential `m` is stably trivial. -/
theorem skCohnGr_graded_mem_stablyTrivial {n : ℕ} (m : Fin n → ℕ)
    {g : SteinbergGroup (Fin n) LVCohnRelK1.CohnTwoF2} (hg : g ∈ skCohnGr_gradedSt m)
    (hk : projection g = 1) : g ∈ skCohnGr_stablyTrivial LVCohnRelK1.CohnTwoF2 n := by
  obtain ⟨y, hy⟩ := skCohnGr_cornerMap_mem_range m hg
  have h2 : n ≤ n + 1 + 1 := by omega
  have hpad := skCohnGr_indexMap_cornerMap_eq m h2 g hk
  rw [← hy, LVStableK2.indexMap_ringMap] at hpad
  have hy1 : projection (indexMap (Fin.castLEEmb h2) y) = 1 := by
    apply LVCohnK2.projection_eq_one_of_ringMap LVCohnDegZero.cohnDegreeZero.subtype
      LVCohnDegZero.cohnDegreeZero.subtype_injective
    rw [hpad]
    exact LVH2GL3.projection_indexMap_eq_one _ hk
  obtain ⟨N, hN, hyN⟩ := LVCohnColimit.skCohnLimK2_stableK2Trivial_degreeZero _ _ hy1
  have e := LVH2GL3.indexMap_castLEEmb_castLEEmb h2 hN g
  rw [← hpad, LVStableK2.indexMap_ringMap, hyN, map_one] at e
  exact skCohnGr_mem_stablyTrivial.mpr ⟨N, h2.trans hN, e.symm⟩

#audit_axioms GroupApproximation.Full.LVCohnGraded.skCohnGr_graded_mem_stablyTrivial

/-- **Graded vanishing, stable form**: if `g ∈ K₂(n, C_2(𝔽₂))` is a graded Steinberg word for some
potential, then `g` dies after padding.  (`simple_kazhdan_sofic_group.tex` l.733-735,
leaf T1b.iii.) -/
theorem skCohnGr_graded_stablyTrivial {n : ℕ} (m : Fin n → ℕ)
    (g : SteinbergGroup (Fin n) LVCohnRelK1.CohnTwoF2) (hg : g ∈ skCohnGr_gradedSt m)
    (hk : projection g = 1) :
    ∃ (N : ℕ) (h : n ≤ N), indexMap (Fin.castLEEmb h) g = 1 :=
  skCohnGr_mem_stablyTrivial.mp (skCohnGr_graded_mem_stablyTrivial m hg hk)

#audit_axioms GroupApproximation.Full.LVCohnGraded.skCohnGr_graded_stablyTrivial

/-- The graded `K₂` elements of `St_n(C_2(𝔽₂))`: elements of `K₂(n, C)` whose Steinberg word is
graded for some potential.  (`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
def skCohnGr_gradedK2Set (n : ℕ) : Set (SteinbergGroup (Fin n) LVCohnRelK1.CohnTwoF2) :=
  {g | projection g = 1 ∧ ∃ m : Fin n → ℕ, g ∈ skCohnGr_gradedSt m}

#audit_axioms GroupApproximation.Full.LVCohnGraded.skCohnGr_gradedK2Set

/-- Membership in `skCohnGr_gradedK2Set`.  (`simple_kazhdan_sofic_group.tex` l.733-735,
leaf T1b.iii.) -/
theorem skCohnGr_mem_gradedK2Set {n : ℕ} {g : SteinbergGroup (Fin n) LVCohnRelK1.CohnTwoF2} :
    g ∈ skCohnGr_gradedK2Set n ↔ projection g = 1 ∧ ∃ m : Fin n → ℕ, g ∈ skCohnGr_gradedSt m :=
  Iff.rfl

#audit_axioms GroupApproximation.Full.LVCohnGraded.skCohnGr_mem_gradedK2Set

/-- **Products of graded `K₂` elements are stably trivial**, even with different potentials.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skCohnGr_closure_gradedK2_le (n : ℕ) :
    Subgroup.closure (skCohnGr_gradedK2Set n) ≤
      skCohnGr_stablyTrivial LVCohnRelK1.CohnTwoF2 n := by
  rw [Subgroup.closure_le]
  intro g hg
  obtain ⟨hk, m, hm⟩ := skCohnGr_mem_gradedK2Set.mp hg
  exact skCohnGr_graded_mem_stablyTrivial m hm hk

#audit_axioms GroupApproximation.Full.LVCohnGraded.skCohnGr_closure_gradedK2_le

end

end GroupApproximation.Full.LVCohnGraded
