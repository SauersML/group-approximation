import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVFrame.Complex
import Mathlib.Algebra.Group.Action.Defs
import GroupApproximation.Meta.AxiomGuard

/-!
# Group actions on ordered 2-complexes, near vertices and cells (leaf T1d)

`simple_kazhdan_sofic_group.tex`, `sec:questions`, l.733-735.  Leaf **T1d** of the
`K₂(4, L) = ⊥` tree (Khanh, arXiv:2609.08428, Thm 5.1) is Brown's presentation theorem
(K. S. Brown, *Presentations for groups acting on simply-connected complexes*, 1984), in the
combinatorial form of Macbeath's theorem.  This file sets up the vocabulary.

* `OrderedTwoComplex.Action X G`: the action of `G` on the vertices maps ordered edges to
  ordered edges and ordered triangles to ordered triangles.  It is placed in the namespace of
  LVFrame's `OrderedTwoComplex` so that the LVAssembly signature `X.Action G` elaborates.
* `Near X a b`: `a = b`, or `a` and `b` span an edge in some orientation.
* `Cell X x y z`: `(x,y,z)` is an ordered triangle, or a degenerate triangle: its three
  vertices are pairwise near and two of them coincide.  The relations of the Brown presentation
  are indexed by cells.
-/

universe u

namespace GroupApproximation.Full.LVFrame.OrderedTwoComplex

variable {V : Type u}

/-- The action of `G` on the vertices preserves ordered edges and ordered triangles
(Khanh, tex l.446). -/
structure Action (X : OrderedTwoComplex V) (G : Type*) [Group G] [MulAction G V] : Prop where
  /-- Translates of ordered edges are ordered edges. -/
  edge_smul : ∀ (g : G) {a b : V}, X.edge a b → X.edge (g • a) (g • b)
  /-- Translates of ordered triangles are ordered triangles. -/
  tri_smul : ∀ (g : G) {a b c : V}, X.tri a b c → X.tri (g • a) (g • b) (g • c)

end GroupApproximation.Full.LVFrame.OrderedTwoComplex

namespace GroupApproximation.Full.LVBrown

open GroupApproximation.Full.LVFrame

variable {V : Type u} (X : OrderedTwoComplex V)

/-- Two vertices are near when they are equal or span an ordered edge in some orientation. -/
def Near (a b : V) : Prop := a = b ∨ X.edge a b ∨ X.edge b a

/-- A (possibly degenerate) 2-cell: an ordered triangle, or three pairwise near vertices two of
which coincide. -/
def Cell (x y z : V) : Prop :=
  X.tri x y z ∨ (Near X x y ∧ Near X y z ∧ Near X x z ∧ (x = y ∨ y = z ∨ x = z))

variable {X}

theorem Near.refl (a : V) : Near X a a := Or.inl rfl

theorem Near.of_eq {a b : V} (h : a = b) : Near X a b := Or.inl h

theorem Near.of_edge {a b : V} (h : X.edge a b) : Near X a b := Or.inr (Or.inl h)

theorem Near.symm {a b : V} (h : Near X a b) : Near X b a := by
  rcases h with h | h | h
  · exact Or.inl h.symm
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)

theorem Cell.near01 {x y z : V} (h : Cell X x y z) : Near X x y := by
  rcases h with h | h
  · exact Near.of_edge (X.tri_edge01 h)
  · exact h.1

theorem Cell.near12 {x y z : V} (h : Cell X x y z) : Near X y z := by
  rcases h with h | h
  · exact Near.of_edge (X.tri_edge12 h)
  · exact h.2.1

theorem Cell.near02 {x y z : V} (h : Cell X x y z) : Near X x z := by
  rcases h with h | h
  · exact Near.of_edge (X.tri_edge02 h)
  · exact h.2.2.1

theorem Cell.of_tri {x y z : V} (h : X.tri x y z) : Cell X x y z := Or.inl h

theorem Cell.of_eq01 {x y z : V} (hxy : x = y) (hyz : Near X y z) : Cell X x y z := by
  subst hxy
  exact Or.inr ⟨Near.refl _, hyz, hyz, Or.inl rfl⟩

theorem Cell.of_eq12 {x y z : V} (hxy : Near X x y) (hyz : y = z) : Cell X x y z := by
  subst hyz
  exact Or.inr ⟨hxy, Near.refl _, hxy, Or.inr (Or.inl rfl)⟩

theorem Cell.of_eq02 {x y z : V} (hxy : Near X x y) (hxz : x = z) : Cell X x y z := by
  subst hxz
  exact Or.inr ⟨hxy, Near.symm hxy, Near.refl _, Or.inr (Or.inr rfl)⟩

variable {G : Type*} [Group G] [MulAction G V]

theorem Near.smul (hX : X.Action G) (g : G) {a b : V} (h : Near X a b) :
    Near X (g • a) (g • b) := by
  rcases h with h | h | h
  · exact Or.inl (by rw [h])
  · exact Or.inr (Or.inl (hX.edge_smul g h))
  · exact Or.inr (Or.inr (hX.edge_smul g h))

theorem near_smul_iff (hX : X.Action G) (g : G) {a b : V} :
    Near X (g • a) (g • b) ↔ Near X a b := by
  refine ⟨fun h => ?_, Near.smul hX g⟩
  have h' := Near.smul hX g⁻¹ h
  rwa [inv_smul_smul, inv_smul_smul] at h'

theorem Cell.smul (hX : X.Action G) (g : G) {x y z : V} (h : Cell X x y z) :
    Cell X (g • x) (g • y) (g • z) := by
  rcases h with h | ⟨h1, h2, h3, h4⟩
  · exact Or.inl (hX.tri_smul g h)
  · refine Or.inr ⟨Near.smul hX g h1, Near.smul hX g h2, Near.smul hX g h3, ?_⟩
    rcases h4 with h4 | h4 | h4
    · exact Or.inl (by rw [h4])
    · exact Or.inr (Or.inl (by rw [h4]))
    · exact Or.inr (Or.inr (by rw [h4]))

theorem cell_smul_iff (hX : X.Action G) (g : G) {x y z : V} :
    Cell X (g • x) (g • y) (g • z) ↔ Cell X x y z := by
  refine ⟨fun h => ?_, Cell.smul hX g⟩
  have h' := Cell.smul hX g⁻¹ h
  rwa [inv_smul_smul, inv_smul_smul, inv_smul_smul] at h'

#audit_axioms GroupApproximation.Full.LVBrown.cell_smul_iff

end GroupApproximation.Full.LVBrown
