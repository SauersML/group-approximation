import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVBrown.BrownCore
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVBrown.Main
import Mathlib.Data.Set.Insert
import Mathlib.Tactic.Choose
import GroupApproximation.Meta.AxiomGuard

/-!
# Brown's criterion, universal-property form (T1d endpoint)

`simple_kazhdan_sofic_group.tex`, `sec:questions`, l.733-735, leaf **T1d** of the
`K₂(4, L) = ⊥` tree (Khanh, arXiv:2609.08428, Thm 5.1; K. S. Brown 1984, Thm 1).  This file
builds on `LVBrown/BrownCore.lean` and `LVBrown/Main.lean`.

Suppose `G` acts on a simply connected ordered 2-complex `X`, transitively on ordered edges
`(v0, v1)` and on ordered triangles `(v0, v1, h•v1)`.  Let `τ` swap `v0` and `v1`, and let `h`
fix `v0`.  Let `f : J →* Q` be a homomorphism on `J = Stab v0` and `t ∈ Q` an element such that
* `t f(a) t⁻¹ = f(τ a τ⁻¹)` for `a ∈ J ∩ Stab v1`,
* `t² = f(τ²)`,
* `t f(h) t = f(h) t f(h)`.

Then `f` extends to a homomorphism `F : G →* Q` with `F τ = t` (`brown_lift`).

Proof.  Take the fundamental domain `F = {v0}`.  Edge transitivity and connectivity show that it
covers `V` (`brownDatum`).  Brown's theorem (`Datum.equiv`) identifies `G` with the Brown group,
whose generators are the `g` with `g•v0` near `v0`.  Every generator has a unique representative
(`rep_exists`, `rep_unique`), and representatives respect the Brown relations (`rel_rep`).  So
the representatives define a homomorphism on the Brown group.
-/

namespace GroupApproximation.Full.LVBrown

open GroupApproximation.Full.LVFrame

/-- Edge transitivity propagates the orbit of `v0` along edge paths. -/
theorem orbit_of_path {G V : Type*} [Group G] [MulAction G V] {X : OrderedTwoComplex V}
    {v0 v1 : V} {τ : G}
    (edge_transitive : ∀ a b, X.edge a b → ∃ g : G, g • v0 = a ∧ g • v1 = b)
    (hτ0 : τ • v0 = v1) {a c : V} (p : X.EdgePath a c) :
    (∃ g : G, g • v0 = a) → ∃ g : G, g • v0 = c := by
  induction p with
  | nil _ => exact id
  | fwd e _ ih =>
    intro _
    obtain ⟨g, -, hg1⟩ := edge_transitive _ _ e
    exact ih ⟨g * τ, by rw [mul_smul, hτ0, hg1]⟩
  | bwd e _ ih =>
    intro _
    obtain ⟨g, hg0, -⟩ := edge_transitive _ _ e
    exact ih ⟨g, hg0⟩

/-- The Brown datum with fundamental domain `{v0}`. -/
def brownDatum {G V : Type*} [Group G] [MulAction G V] {X : OrderedTwoComplex V}
    (hX : X.Action G) (hconn : X.Connected) {v0 v1 : V} {τ : G}
    (edge_transitive : ∀ a b, X.edge a b → ∃ g : G, g • v0 = a ∧ g • v1 = b)
    (hτ0 : τ • v0 = v1) : Datum X G where
  F := {v0}
  action := hX
  cover v := by
    obtain ⟨p⟩ := hconn v0 v
    obtain ⟨g, hg⟩ := orbit_of_path edge_transitive hτ0 p ⟨1, one_smul G v0⟩
    exact ⟨g, v0, Set.mem_singleton v0, hg⟩
  base := v0
  base_mem := Set.mem_singleton v0
  connected y hy := by
    have hy' : y = v0 := Set.mem_singleton_iff.mp hy
    subst hy'
    exact Relation.ReflTransGen.refl

/-- A Brown generator for the fundamental domain `{v0}` moves `v0` near `v0`. -/
theorem near_of_mem {G V : Type*} [Group G] [MulAction G V] {X : OrderedTwoComplex V}
    {F : Set V} {v0 : V} (hF : F = {v0}) {g : G} (h : ∃ x ∈ F, ∃ y ∈ F, Near X x (g • y)) :
    Near X v0 (g • v0) := by
  obtain ⟨x, hx, y, hy, hn⟩ := h
  rw [hF, Set.mem_singleton_iff] at hx hy
  rw [hx, hy] at hn
  exact hn

/-- **Brown's criterion** (Khanh, Thm 5.1; Brown 1984, Thm 1), leaf T1d.  A homomorphism on the
vertex stabilizer that satisfies the edge, square and braid relations extends to `G`. -/
theorem brown_lift {G V : Type} [Group G] [MulAction G V]
    (X : OrderedTwoComplex V) (hX : X.Action G) (hsc : X.SimplyConnected)
    (v0 v1 : V) (he : X.edge v0 v1)
    (edge_transitive : ∀ a b, X.edge a b → ∃ g : G, g • v0 = a ∧ g • v1 = b)
    (τ h : G) (hτ0 : τ • v0 = v1) (hτ1 : τ • v1 = v0)
    (hh0 : h • v0 = v0) (hhh : h * h = 1) (hbraid : τ * h * τ = h * τ * h)
    (tri_transitive : ∀ a b c, X.tri a b c → ∃ g : G, g • v0 = a ∧ g • v1 = b ∧ g • (h • v1) = c)
    (hgen : Subgroup.closure ((MulAction.stabilizer G v0 : Set G) ∪ {τ}) = ⊤)
    {Q : Type} [Group Q] (f : MulAction.stabilizer G v0 →* Q) (t : Q)
    (hedge : ∀ a b : MulAction.stabilizer G v0, (a : G) • v1 = v1 → (b : G) = τ * a * τ⁻¹ →
      t * f a * t⁻¹ = f b)
    (hτ2 : (τ * τ) • v0 = v0) (ht2 : t * t = f ⟨τ * τ, hτ2⟩)
    (hbr : t * f ⟨h, hh0⟩ * t = f ⟨h, hh0⟩ * t * f ⟨h, hh0⟩) :
    ∃ F : G →* Q, (∀ j, F j = f j) ∧ F τ = t := by
  -- `h² = 1` and generation are not needed: Brown's theorem supplies the presentation.
  have _ := hhh
  have _ := hgen
  obtain ⟨D, hDF⟩ : ∃ D : Datum X G, D.F = {v0} :=
    ⟨brownDatum hX hsc.1 edge_transitive hτ0, rfl⟩
  have hex : ∀ s : D.Gen, ∃ q, Rep v0 τ f t s.1 q := fun s =>
    rep_exists edge_transitive hτ0 hτ2 f t (near_of_mem hDF s.2)
  choose ψ hψ using hex
  have hrels : ∀ r ∈ D.rels, FreeGroup.lift ψ r = 1 := by
    rintro r ⟨a, b, c, hab, ⟨x, hx, y, hy, z, hz, hcell⟩, rfl⟩
    rw [hDF, Set.mem_singleton_iff] at hx hy hz
    rw [hx, hy, hz] at hcell
    simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
    rw [mul_inv_eq_one]
    exact rep_unique hτ0 hτ1 hh0 hbraid f t hedge hτ2 ht2 hbr
      (rel_rep hX hτ0 hτ1 hh0 hbraid tri_transitive f t hedge hτ2 ht2 hbr (hψ a) (hψ b) hab
        hcell) (hψ c)
  have hv0 : v0 ∈ D.F := by
    rw [hDF]
    exact Set.mem_singleton v0
  refine ⟨(PresentedGroup.toGroup hrels).comp (D.equiv hsc).symm.toMonoidHom, fun j => ?_, ?_⟩
  · have hnj : Near X v0 ((j : G) • v0) := Near.of_eq (smul_stab j).symm
    obtain ⟨s, hs1, hsq⟩ : ∃ s : D.Gen,
        (D.equiv hsc).symm (j : G) = PresentedGroup.of s ∧ s.1 = (j : G) :=
      ⟨D.mkGen (j : G) hv0 hv0 hnj, D.equiv_symm_gen hsc (D.mkGen (j : G) hv0 hv0 hnj), rfl⟩
    show PresentedGroup.toGroup hrels ((D.equiv hsc).symm (j : G)) = f j
    rw [hs1, PresentedGroup.toGroup.of]
    exact rep_unique hτ0 hτ1 hh0 hbraid f t hedge hτ2 ht2 hbr (hψ s)
      (rep_congr (rep_of_mem f j) hsq.symm rfl)
  · have hτe : X.edge v0 (τ • v0) := by
      rw [hτ0]
      exact he
    have hnτ : Near X v0 (τ • v0) := Near.of_edge hτe
    obtain ⟨s, hs1, hsq⟩ : ∃ s : D.Gen, (D.equiv hsc).symm τ = PresentedGroup.of s ∧ s.1 = τ :=
      ⟨D.mkGen τ hv0 hv0 hnτ, D.equiv_symm_gen hsc (D.mkGen τ hv0 hv0 hnτ), rfl⟩
    show PresentedGroup.toGroup hrels ((D.equiv hsc).symm τ) = t
    rw [hs1, PresentedGroup.toGroup.of]
    exact rep_unique hτ0 hτ1 hh0 hbraid f t hedge hτ2 ht2 hbr (hψ s)
      (rep_congr (rep_tau τ f t) hsq.symm rfl)

#audit_axioms GroupApproximation.Full.LVBrown.brown_lift

end GroupApproximation.Full.LVBrown
