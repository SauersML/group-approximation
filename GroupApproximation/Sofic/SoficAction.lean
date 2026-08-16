import GroupApproximation.Sofic.Sofic
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.Perm.Basic

/-!
# Sofic actions on sets

Gao--Kunnawalkam Elayavalli--Patchell (arXiv:2401.04945, Definition 2.1) call an
action `G ↷ X` *sofic* when every finite window admits a finite permutation
model together with injective charts of the window into a finite set which
intertwine the tested translations.  The approximating map `φ : G → Sym A` is
**not** required to be free, which is exactly why an action can be sofic without
the acting group being known to be sofic.

`SoficActionModel` is the model data and `IsSoficAction` the local definition.
`SoficActionModel.restrict` records that a model for one window serves any
smaller window, so soficity may be tested on any cofinal family of windows.
The finite-orbit constructions built on top of it live in
`Sofic.SoficActionFiniteOrbits`.

Unlike `IsSofic`, this file keeps the model set and the chart target in the
universe of `X`, so the normalized Hamming distance is redeveloped here for a
bare `Fintype` rather than reusing the `Type`-valued `FiniteModel` bundle.
-/

namespace GroupApproximation

universe u v

/-! ## Normalized Hamming distance on an arbitrary finite type -/

/-- Normalized Hamming distance between permutations of a finite type.  This is
`hammingDistance` transported off the `Type 0`-valued `FiniteModel` bundle. -/
noncomputable def permDist {A : Type*} [Fintype A] [DecidableEq A]
    (p q : Equiv.Perm A) : ℝ :=
  ((Finset.univ.filter fun a => p a ≠ q a).card : ℝ) / Fintype.card A

theorem permDist_nonneg {A : Type*} [Fintype A] [DecidableEq A]
    (p q : Equiv.Perm A) : 0 ≤ permDist p q :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

@[simp] theorem permDist_self {A : Type*} [Fintype A] [DecidableEq A]
    (p : Equiv.Perm A) : permDist p p = 0 := by
  simp [permDist]

theorem permDist_eq_zero_of_eq {A : Type*} [Fintype A] [DecidableEq A]
    {p q : Equiv.Perm A} (h : p = q) : permDist p q = 0 := by
  subst h; simp

/-! ## Finite orbit models -/

/-- A finite orbit-approximation model for `G ↷ X` on the window `(F, E)` at
tolerance `ε`.  This is Definition 2.1 of Gao--Kunnawalkam Elayavalli--Patchell:
a finite model set `Site`, an `(F, ε)`-multiplicative unital map into its
permutations, a large set `good` of model points, and injective charts of `E`
into a finite target which intertwine the tested translations. -/
structure SoficActionModel (G : Type u) [Group G] (X : Type v) [MulAction G X]
    (F : Finset G) (E : Finset X) (ε : ℝ) where
  /-- The finite model set, written `A` in the source. -/
  Site : Type v
  siteFintype : Fintype Site
  siteDecEq : DecidableEq Site
  siteNonempty : 0 < Fintype.card Site
  /-- The approximate action `φ : G → Sym(A)`. -/
  act : G → Equiv.Perm Site
  act_one : act 1 = 1
  act_mul : ∀ g ∈ F, ∀ h ∈ F,
    permDist (act (g * h)) (act g * act h) ≤ ε
  /-- The set `S` of good model points. -/
  good : Finset Site
  good_card : (1 - ε) * (Fintype.card Site : ℝ) ≤ (good.card : ℝ)
  /-- The finite chart target `B`. -/
  Chart : Type v
  chartFintype : Fintype Chart
  /-- The charts `π_s : E ↪ B`, defined on all of `X` for convenience and
  constrained only on the window. -/
  chart : Site → X → Chart
  chart_inj : ∀ s ∈ good, ∀ x ∈ E, ∀ y ∈ E, chart s x = chart s y → x = y
  chart_equivariant : ∀ g ∈ F, ∀ s ∈ good, act g s ∈ good →
    ∀ x ∈ E, g⁻¹ • x ∈ E → chart (act g s) x = chart s (g⁻¹ • x)

attribute [instance] SoficActionModel.siteFintype SoficActionModel.siteDecEq
  SoficActionModel.chartFintype

/-- Local definition of a sofic action: every finite window has arbitrarily
accurate orbit-approximation models. -/
def IsSoficAction (G : Type u) [Group G] (X : Type v) [MulAction G X] : Prop :=
  ∀ (F : Finset G) (E : Finset X) (ε : ℝ), 0 < ε →
    Nonempty (SoficActionModel G X F E ε)

namespace SoficActionModel

variable {G : Type u} [Group G] {X : Type v} [MulAction G X]

/-- A model for a window serves every smaller window at the same tolerance.
Hence soficity may be tested along any cofinal family of windows. -/
def restrict {F F' : Finset G} {E E' : Finset X} {ε : ℝ}
    (M : SoficActionModel G X F E ε) (hF : F' ⊆ F) (hE : E' ⊆ E) :
    SoficActionModel G X F' E' ε where
  Site := M.Site
  siteFintype := M.siteFintype
  siteDecEq := M.siteDecEq
  siteNonempty := M.siteNonempty
  act := M.act
  act_one := M.act_one
  act_mul := fun g hg h hh => M.act_mul g (hF hg) h (hF hh)
  good := M.good
  good_card := M.good_card
  Chart := M.Chart
  chartFintype := M.chartFintype
  chart := M.chart
  chart_inj := fun s hs x hx y hy h => M.chart_inj s hs x (hE hx) y (hE hy) h
  chart_equivariant := fun g hg s hs hgs x hx hgx =>
    M.chart_equivariant g (hF hg) s hs hgs x (hE hx) (hE hgx)

end SoficActionModel


end GroupApproximation
