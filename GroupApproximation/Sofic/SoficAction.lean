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



/-! ## Restriction along a homomorphism and subgroup covers -/

section Transfer

universe w

variable {G : Type u} [Group G] {H : Type w} [Group H] {X : Type v}

/-- Soficity of an action restricts along any homomorphism into the acting
group. -/
theorem IsSoficAction.compHom [MulAction H X] (f : G →* H)
    (hH : IsSoficAction H X) :
    @IsSoficAction G _ X (MulAction.compHom X f) := by
  classical
  letI : MulAction G X := MulAction.compHom X f
  intro F E ε hε
  obtain ⟨M⟩ := hH (F.image f) E ε hε
  exact ⟨{
    Site := M.Site
    siteFintype := M.siteFintype
    siteDecEq := M.siteDecEq
    siteNonempty := M.siteNonempty
    act := fun g => M.act (f g)
    act_one := by rw [map_one]; exact M.act_one
    act_mul := by
      intro g hg h hh
      rw [map_mul]
      exact M.act_mul (f g) (Finset.mem_image_of_mem _ hg) (f h)
        (Finset.mem_image_of_mem _ hh)
    good := M.good
    good_card := M.good_card
    Chart := M.Chart
    chartFintype := M.chartFintype
    chart := M.chart
    chart_inj := M.chart_inj
    chart_equivariant := by
      intro g hg s hs hgs x hx hgx
      have heq : ((f g)⁻¹ • x : X) = (g⁻¹ • x : X) := by
        show ((f g)⁻¹ • x : X) = (f g⁻¹ • x : X)
        rw [map_inv]
      have hgx' : ((f g)⁻¹ • x : X) ∈ E := by rw [heq]; exact hgx
      have hres := M.chart_equivariant (f g) (Finset.mem_image_of_mem _ hg) s hs
        hgs x hx hgx'
      rw [heq] at hres
      exact hres }⟩

/-- Soficity of an action transfers along a group isomorphism which implements
the same action. -/
theorem IsSoficAction.of_mulEquiv [MulAction G X] [MulAction H X] (e : G ≃* H)
    (hcompat : ∀ (g : G) (x : X), (e g : H) • x = g • x)
    (hG : IsSoficAction G X) : IsSoficAction H X := by
  classical
  intro F E ε hε
  obtain ⟨M⟩ := hG (F.image e.symm) E ε hε
  have hsmul : ∀ (h : H) (x : X), (e.symm h) • x = h • x := by
    intro h x
    rw [← hcompat (e.symm h) x, MulEquiv.apply_symm_apply]
  exact ⟨{
    Site := M.Site
    siteFintype := M.siteFintype
    siteDecEq := M.siteDecEq
    siteNonempty := M.siteNonempty
    act := fun h => M.act (e.symm h)
    act_one := by rw [map_one]; exact M.act_one
    act_mul := by
      intro g hg h hh
      rw [map_mul]
      exact M.act_mul _ (Finset.mem_image_of_mem _ hg) _
        (Finset.mem_image_of_mem _ hh)
    good := M.good
    good_card := M.good_card
    Chart := M.Chart
    chartFintype := M.chartFintype
    chart := M.chart
    chart_inj := M.chart_inj
    chart_equivariant := by
      intro h hh s hs hgs x hx hgx
      have heq : ((e.symm h)⁻¹ • x : X) = (h⁻¹ • x : X) := by
        rw [← map_inv, hsmul]
      have hgx' : ((e.symm h)⁻¹ • x : X) ∈ E := by rw [heq]; exact hgx
      have hres := M.chart_equivariant (e.symm h)
        (Finset.mem_image_of_mem _ hh) s hs hgs x hx hgx'
      rw [heq] at hres
      exact hres }⟩

variable [MulAction G X]

/-- **Lemma 13.4 in general form.**  If every finite subset of `G` lies in a
subgroup whose restricted action is sofic, then the action is sofic.  The model
for the subgroup serves the ambient group directly: extend the approximating map
by the identity outside the subgroup, and every condition tested on the finite
set is unchanged. -/
theorem isSoficAction_of_subgroup_cover
    (h : ∀ F : Finset G, ∃ K : Subgroup G, (∀ g ∈ F, g ∈ K) ∧
      IsSoficAction K X) :
    IsSoficAction G X := by
  classical
  intro F E ε hε
  obtain ⟨K, hFK, hK⟩ := h F
  set F' : Finset K := F.attach.image (fun p => (⟨p.1, hFK p.1 p.2⟩ : K)) with hF'
  obtain ⟨M⟩ := hK F' E ε hε
  have hmemF' : ∀ g (hg : g ∈ F), (⟨g, hFK g hg⟩ : K) ∈ F' := by
    intro g hg
    rw [hF']
    exact Finset.mem_image_of_mem _ (Finset.mem_attach _ ⟨g, hg⟩)
  exact ⟨{
    Site := M.Site
    siteFintype := M.siteFintype
    siteDecEq := M.siteDecEq
    siteNonempty := M.siteNonempty
    act := fun g => if hg : g ∈ K then M.act ⟨g, hg⟩ else 1
    act_one := by
      rw [dif_pos K.one_mem]
      have hone : (⟨(1 : G), K.one_mem⟩ : K) = 1 := rfl
      rw [hone]
      exact M.act_one
    act_mul := by
      intro g hg h hh
      have hgK : g ∈ K := hFK g hg
      have hhK : h ∈ K := hFK h hh
      rw [dif_pos hgK, dif_pos hhK, dif_pos (K.mul_mem hgK hhK)]
      have hsplit : (⟨g * h, K.mul_mem hgK hhK⟩ : K) = ⟨g, hgK⟩ * ⟨h, hhK⟩ := rfl
      rw [hsplit]
      exact M.act_mul _ (hmemF' g hg) _ (hmemF' h hh)
    good := M.good
    good_card := M.good_card
    Chart := M.Chart
    chartFintype := M.chartFintype
    chart := M.chart
    chart_inj := M.chart_inj
    chart_equivariant := by
      intro g hg s hs hgs x hx hgx
      have hgK : g ∈ K := hFK g hg
      rw [dif_pos hgK] at hgs ⊢
      exact M.chart_equivariant ⟨g, hgK⟩ (hmemF' g hg) s hs hgs x hx hgx }⟩

end Transfer

end GroupApproximation
