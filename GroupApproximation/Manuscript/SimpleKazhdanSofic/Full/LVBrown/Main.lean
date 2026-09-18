import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVBrown.Lifts
import Mathlib.Algebra.Group.Subgroup.Pointwise
import GroupApproximation.Meta.AxiomGuard

/-!
# Brown's presentation theorem, combinatorial form (T1d)

`simple_kazhdan_sofic_group.tex`, `sec:questions`, l.733-735, leaf **T1d** (K. S. Brown 1984,
Thm 1; A. M. Macbeath 1964).  This file builds on `LVBrown/Lifts.lean`.

Let `D : Datum X G` be a Brown datum for an action on a simply connected ordered 2-complex.
Then the canonical homomorphism `D.toG : D.Pres →* G` from the Brown group is bijective
(`toG_injective`, `toG_surjective`), and `D.equiv hsc : D.Pres ≃* G`.

Proof.  A state `s` is *reachable* when some edge path from the base vertex lifts from the
base state `(1, base)` to `s`.  Every state `(π, y)` with `y ∈ F` is reachable.  This is proved by
induction over words in the generators, using the connectivity of `F`.
* Injectivity.  Suppose `toG π = 1`.  Reach `(π, base)` along a loop at `base`.  Simple
  connectivity and homotopy invariance of lifts replace the loop by the constant path.  Hence
  `π = [t]` with `t = 1`.
* Surjectivity.  Lift a path from `base` to `g • base`.
-/

namespace GroupApproximation.Full.LVBrown

open GroupApproximation.Full.LVFrame
open GroupApproximation.Full.LVFrame.OrderedTwoComplex

universe u

variable {V : Type u} {X : OrderedTwoComplex V} {G : Type*} [Group G] [MulAction G V]

namespace Datum

variable (D : Datum X G)

/-- One covering step extends a lift by at most one edge. -/
theorem exists_lifts_extend {a c : V} (γ : X.EdgePath a c) {s s₁ s₂ : D.State}
    (h : D.Lifts γ s s₁) (h₁₂ : D.R s₁ s₂) :
    ∃ (v : V) (γ' : X.EdgePath a v), D.Lifts γ' s s₂ := by
  obtain ⟨-, -, -, hpos₁⟩ := D.lifts_ends γ h
  have hs₂ : s₂.2 ∈ D.F := h₁₂.2.1
  have hnil : D.Lifts (EdgePath.nil (D.pos s₂)) s₂ s₂ :=
    (D.lifts_nil (D.pos s₂) s₂ s₂).mpr ⟨rfl, D.rel_refl s₂.1 hs₂, rfl⟩
  rcases D.rel_near_pos h₁₂ with he | he | he
  · exact ⟨c, γ, D.lifts_of_end γ h h₁₂ he⟩
  · rw [hpos₁] at he
    refine ⟨D.pos s₂, γ.append (EdgePath.fwd he (EdgePath.nil (D.pos s₂))), ?_⟩
    exact (D.lifts_append γ (EdgePath.fwd he (EdgePath.nil (D.pos s₂))) s s₂).mpr
      ⟨s₁, h, (D.lifts_fwd he (EdgePath.nil (D.pos s₂)) s₁ s₂).mpr ⟨hpos₁, s₂, h₁₂, hnil⟩⟩
  · rw [hpos₁] at he
    refine ⟨D.pos s₂, γ.append (EdgePath.bwd he (EdgePath.nil (D.pos s₂))), ?_⟩
    exact (D.lifts_append γ (EdgePath.bwd he (EdgePath.nil (D.pos s₂))) s s₂).mpr
      ⟨s₁, h, (D.lifts_bwd he (EdgePath.nil (D.pos s₂)) s₁ s₂).mpr ⟨hpos₁, s₂, h₁₂, hnil⟩⟩

/-- The base state `(1, base)`. -/
abbrev start : D.State := (1, D.base)

theorem pos_start : D.pos D.start = D.base := by
  show D.toG 1 • D.base = D.base
  rw [map_one, one_smul]

/-- A state is reachable when some edge path from the base vertex lifts from the base state
to it. -/
def Reach (s : D.State) : Prop :=
  ∃ (v : V) (γ : X.EdgePath D.base v), D.Lifts γ D.start s

theorem reach_step {s₁ s₂ : D.State} (h : D.Reach s₁) (h₁₂ : D.R s₁ s₂) : D.Reach s₂ := by
  obtain ⟨v, γ, hγ⟩ := h
  exact D.exists_lifts_extend γ hγ h₁₂

theorem reach_start : D.Reach D.start :=
  ⟨D.base, EdgePath.nil D.base,
    (D.lifts_nil D.base D.start D.start).mpr ⟨D.pos_start, D.rel_refl 1 D.base_mem, D.pos_start⟩⟩

/-- Moving inside the frame `σ`, from the base vertex. -/
theorem reach_of_base {σ : D.Pres} {y : V} (h : D.Reach (σ, D.base))
    (hc : Relation.ReflTransGen (fun u w : V => u ∈ D.F ∧ w ∈ D.F ∧ Near X u w) D.base y) :
    D.Reach (σ, y) := by
  induction hc with
  | refl => exact h
  | tail _ hbc ih =>
    exact D.reach_step (s₁ := (σ, _)) (s₂ := (σ, _)) ih
      (D.rel_same_frame σ hbc.1 hbc.2.1 hbc.2.2)

/-- Moving inside the frame `σ`, back to the base vertex. -/
theorem reach_base_of_frame {σ : D.Pres} {y : V}
    (hc : Relation.ReflTransGen (fun u w : V => u ∈ D.F ∧ w ∈ D.F ∧ Near X u w) D.base y) :
    D.Reach (σ, y) → D.Reach (σ, D.base) := by
  induction hc with
  | refl => exact id
  | tail _ hbc ih =>
    exact fun h => ih (D.reach_step (s₁ := (σ, _)) (s₂ := (σ, _)) h
      (D.rel_same_frame σ hbc.2.1 hbc.1 hbc.2.2.symm))

/-- Reachability of one state of a frame propagates to the whole frame. -/
theorem reach_frame {σ : D.Pres} {y : V} (hy : y ∈ D.F) (h : D.Reach (σ, y)) :
    ∀ z ∈ D.F, D.Reach (σ, z) := fun z hz =>
  D.reach_of_base (D.reach_base_of_frame (D.connected y hy) h) (D.connected z hz)

theorem reach_one : ∀ y ∈ D.F, D.Reach ((1 : D.Pres), y) :=
  D.reach_frame (σ := 1) D.base_mem D.reach_start

theorem reach_mul_gen (π g : D.Pres) (hg : g ∈ Set.range (PresentedGroup.of : D.Gen → D.Pres))
    (h : ∀ y ∈ D.F, D.Reach (π, y)) : ∀ y ∈ D.F, D.Reach (π * g, y) := by
  obtain ⟨t, rfl⟩ := hg
  obtain ⟨x₀, hx₀, y₀, hy₀, hn⟩ := t.2
  have hr : D.Rel π x₀ (π * PresentedGroup.of t) y₀ := ⟨hx₀, hy₀, t, rfl, hn⟩
  exact D.reach_frame hy₀
    (D.reach_step (s₁ := (π, x₀)) (s₂ := (π * PresentedGroup.of t, y₀)) (h x₀ hx₀) hr)

theorem reach_mul_inv_gen (π g : D.Pres)
    (hg : g ∈ Set.range (PresentedGroup.of : D.Gen → D.Pres))
    (h : ∀ y ∈ D.F, D.Reach (π, y)) : ∀ y ∈ D.F, D.Reach (π * g⁻¹, y) := by
  obtain ⟨t, rfl⟩ := hg
  obtain ⟨x₀, hx₀, y₀, hy₀, hn⟩ := t.2
  have hr : D.Rel (π * (PresentedGroup.of t)⁻¹) x₀ π y₀ :=
    ⟨hx₀, hy₀, t, (inv_mul_cancel_right π (PresentedGroup.of t)).symm, hn⟩
  exact D.reach_frame hx₀
    (D.reach_step (s₁ := (π, y₀)) (s₂ := (π * (PresentedGroup.of t)⁻¹, x₀)) (h y₀ hy₀)
      (Rel.symm D hr))

/-- Every state over the fundamental domain is reachable. -/
theorem reach_all (π : D.Pres) : ∀ y ∈ D.F, D.Reach (π, y) := by
  have hπ : π ∈ Subgroup.closure (Set.range (PresentedGroup.of : D.Gen → D.Pres)) := by
    rw [PresentedGroup.closure_range_of]
    exact Subgroup.mem_top π
  exact Subgroup.closure_induction_right (p := fun π _ => ∀ y ∈ D.F, D.Reach (π, y))
    D.reach_one (fun x _ g hg ih => D.reach_mul_gen x g hg ih)
    (fun x _ g hg ih => D.reach_mul_inv_gen x g hg ih) hπ

/-- **Brown's theorem, injectivity.** -/
theorem toG_injective (hsc : X.SimplyConnected) : Function.Injective D.toG := by
  refine (injective_iff_map_eq_one D.toG).mpr fun π hπ => ?_
  obtain ⟨v, γ, hγ⟩ := D.reach_all π D.base D.base_mem
  obtain ⟨-, -, -, hv⟩ := D.lifts_ends γ hγ
  have hv' : v = D.base := by
    rw [← hv]
    show D.toG π • D.base = D.base
    rw [hπ, one_smul]
  subst hv'
  have h0 : D.Lifts (EdgePath.nil D.base) D.start (π, D.base) :=
    (D.lifts_iff_of_homotopic (hsc.homotopic γ (EdgePath.nil D.base)) D.start (π, D.base)).mp hγ
  obtain ⟨-, ⟨-, -, t, ht, -⟩, -⟩ := (D.lifts_nil D.base D.start (π, D.base)).mp h0
  have ht' : π = PresentedGroup.of t := by
    rw [← one_mul (PresentedGroup.of t : D.Pres)]
    exact ht
  have h1 : t.1 = 1 := by
    rw [← D.toG_of t, ← ht']
    exact hπ
  rw [ht']
  exact D.of_eq_one t h1

/-- **Brown's theorem, surjectivity.** -/
theorem toG_surjective (hsc : X.SimplyConnected) : Function.Surjective D.toG := by
  intro g
  obtain ⟨γ⟩ := hsc.1 D.base (g • D.base)
  obtain ⟨s', hs'⟩ := D.exists_lifts γ D.start D.base_mem D.pos_start
  obtain ⟨-, -, hy', hpos'⟩ := D.lifts_ends γ hs'
  have hpos'' : D.toG s'.1 • s'.2 = g • D.base := hpos'
  have hn : Near X D.base ((g⁻¹ * D.toG s'.1) • s'.2) := by
    refine Near.of_eq ?_
    rw [mul_smul, hpos'', inv_smul_smul]
  refine ⟨s'.1 * (PresentedGroup.of (D.mkGen (g⁻¹ * D.toG s'.1) D.base_mem hy' hn))⁻¹, ?_⟩
  rw [map_mul, map_inv, D.toG_of]
  show D.toG s'.1 * (g⁻¹ * D.toG s'.1)⁻¹ = g
  rw [mul_inv_rev, inv_inv, mul_inv_cancel_left]

/-- **Brown's presentation theorem** (Brown 1984, Thm 1): the Brown group of a datum on a simply
connected complex is isomorphic to `G`. -/
noncomputable def equiv (hsc : X.SimplyConnected) : D.Pres ≃* G :=
  MulEquiv.ofBijective D.toG ⟨D.toG_injective hsc, D.toG_surjective hsc⟩

theorem equiv_symm_gen (hsc : X.SimplyConnected) (t : D.Gen) :
    (D.equiv hsc).symm t.1 = PresentedGroup.of t := by
  apply D.toG_injective hsc
  rw [D.toG_of]
  exact MulEquiv.ofBijective_apply_symm_apply D.toG _

#audit_axioms GroupApproximation.Full.LVBrown.Datum.equiv_symm_gen

end Datum

end GroupApproximation.Full.LVBrown
