import GroupApproximation.BooneHigmanLinear.CharZero.BTri.Amalgam
import GroupApproximation.BooneHigmanLinear.CharZero.BTri.Building
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.Coset.Defs
import GroupApproximation.Meta.AxiomGuard

/-!
# The development of a triangle action (Z1-base, piece Z.5, part 2)

`TriangleAction G Γ s τ` packages the hypotheses on an action of a group `G` on a graph `Γ`:
* the action preserves adjacency and a type function `τ : V → Fin 3`;
* adjacent vertices have different types;
* the standard triangle `s 0, s 1, s 2` has types `0, 1, 2`;
* every edge and every triangle is `G`-equivalent to the face of `s` of the same types.
Piece Z.3 (lane fix-bh-a) proves these for `SL₃(B)` on the lattice building.

Let `P i` be the stabilizer of `s i` and `Am P` their amalgam (`BTri/Amalgam.lean`). The
development has vertices `(i, ĝ · P̂ᵢ)`, cosets of the image of `P i` in `Am P`. Two of them are
adjacent when their types differ and the cosets meet. It projects to `Γ` by
`(i, ĝ P̂ᵢ) ↦ amEval ĝ • s i`, and this projection is a covering:
* `hatLift_exists`: an edge at the image lifts to an edge;
* `hatLift_unique`: the lift is unique;
* `hatLift_tri`: triangles lift to triangles.
Path lifting and the main theorem are in `BTri/Lifting.lean`.
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace BTri

section Develop

variable (G : Type*) [Group G] {V : Type*} [MulAction G V] (Γ : SimpleGraph V)
  (s : Fin 3 → V) (τ : V → Fin 3)

/-- **A type-preserving action whose standard triangle is a strict fundamental domain.** -/
structure TriangleAction : Prop where
  adj_smul : ∀ (g : G) (x y : V), Γ.Adj (g • x) (g • y) ↔ Γ.Adj x y
  type_smul : ∀ (g : G) (x : V), τ (g • x) = τ x
  type_std : ∀ i, τ (s i) = i
  type_adj : ∀ x y, Γ.Adj x y → τ x ≠ τ y
  std_adj : ∀ i j, i ≠ j → Γ.Adj (s i) (s j)
  edge : ∀ x y, Γ.Adj x y → ∃ g : G, g • x = s (τ x) ∧ g • y = s (τ y)
  chamber : ∀ x y z, Γ.Adj x y → Γ.Adj y z → Γ.Adj x z →
    ∃ g : G, g • x = s (τ x) ∧ g • y = s (τ y) ∧ g • z = s (τ z)

/-- The vertex stabilizers. -/
abbrev stabs : Fin 3 → Subgroup G :=
  fun i => MulAction.stabilizer G (s i)

/-- The vertices of the development. -/
abbrev Hat : Type _ :=
  Σ i : Fin 3, Am (stabs G s) ⧸ (amOf (stabs G s) i).range

variable {G s}

/-- The vertex `(i, ĝ P̂ᵢ)`. -/
def mkHat (i : Fin 3) (g : Am (stabs G s)) : Hat G s :=
  ⟨i, QuotientGroup.mk g⟩

theorem hat_exists_mk (v : Hat G s) : ∃ g, v = mkHat v.1 g := by
  obtain ⟨i, q⟩ := v
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨g, rfl⟩

#audit_axioms hat_exists_mk

theorem mkHat_eq_iff {i : Fin 3} {g h : Am (stabs G s)} :
    mkHat i g = mkHat i h ↔ g⁻¹ * h ∈ (amOf (stabs G s) i).range := by
  rw [mkHat, mkHat, Sigma.mk.inj_iff, heq_iff_eq, QuotientGroup.eq]
  exact ⟨fun h' => h'.2, fun h' => ⟨rfl, h'⟩⟩

#audit_axioms mkHat_eq_iff

theorem mkHat_mul_amOf (i : Fin 3) (g : Am (stabs G s)) (a : stabs G s i) :
    mkHat i (g * amOf (stabs G s) i a) = mkHat i g := by
  rw [mkHat_eq_iff, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
  exact ⟨a⁻¹, map_inv _ a⟩

#audit_axioms mkHat_mul_amOf

theorem proj_wd (i : Fin 3) (g h : Am (stabs G s))
    (hgh : g⁻¹ * h ∈ (amOf (stabs G s) i).range) :
    amEval (stabs G s) g • s i = amEval (stabs G s) h • s i := by
  obtain ⟨a, ha⟩ := hgh
  have hh : h = g * amOf (stabs G s) i a := by rw [ha, mul_inv_cancel_left]
  rw [hh, map_mul, amEval_amOf, mul_smul, MulAction.mem_stabilizer_iff.mp a.2]

#audit_axioms proj_wd

variable (G s)

/-- The projection `(i, ĝ P̂ᵢ) ↦ amEval ĝ • s i`. -/
def hatProj (v : Hat G s) : V :=
  Quotient.liftOn' v.2 (fun g => amEval (stabs G s) g • s v.1) fun g h hgh =>
    proj_wd v.1 g h (QuotientGroup.leftRel_apply.mp hgh)

/-- Adjacency in the development: distinct types, meeting cosets. -/
def HatAdj (v w : Hat G s) : Prop :=
  v.1 ≠ w.1 ∧ ∃ k : Am (stabs G s), mkHat v.1 k = v ∧ mkHat w.1 k = w

variable {G s}

@[simp] theorem hatProj_mk (i : Fin 3) (g : Am (stabs G s)) :
    hatProj G s (mkHat i g) = amEval (stabs G s) g • s i :=
  rfl

theorem hatAdj_symm {v w : Hat G s} (h : HatAdj G s v w) : HatAdj G s w v :=
  ⟨h.1.symm, h.2.imp fun _ hk => ⟨hk.2, hk.1⟩⟩

#audit_axioms hatAdj_symm

/-- The standard common vertex: `(i, ĝ)` and `(j, ĝ)` are adjacent for `i ≠ j`. -/
theorem hatAdj_mk (g : Am (stabs G s)) {i j : Fin 3} (hij : i ≠ j) :
    HatAdj G s (mkHat i g) (mkHat j g) :=
  ⟨hij, g, rfl, rfl⟩

#audit_axioms hatAdj_mk

variable {Γ τ}

theorem hatProj_type (hA : TriangleAction G Γ s τ) (v : Hat G s) : τ (hatProj G s v) = v.1 := by
  obtain ⟨i, q⟩ := v
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  show τ (amEval (stabs G s) g • s i) = i
  rw [hA.type_smul, hA.type_std]

#audit_axioms hatProj_type

theorem hatProj_adj (hA : TriangleAction G Γ s τ) {v w : Hat G s} (h : HatAdj G s v w) :
    Γ.Adj (hatProj G s v) (hatProj G s w) := by
  obtain ⟨hne, k, hv, hw⟩ := h
  rw [← hv, ← hw, hatProj_mk, hatProj_mk, hA.adj_smul]
  exact hA.std_adj _ _ hne

#audit_axioms hatProj_adj

/-- **Edges lift.** -/
theorem hatLift_exists (hA : TriangleAction G Γ s τ) (v : Hat G s) {y : V}
    (hy : Γ.Adj (hatProj G s v) y) : ∃ w, HatAdj G s v w ∧ hatProj G s w = y := by
  obtain ⟨i, q⟩ := v
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  change Γ.Adj (amEval (stabs G s) g • s i) y at hy
  have hy' : Γ.Adj (s i) ((amEval (stabs G s) g)⁻¹ • y) := by
    rw [← hA.adj_smul (amEval (stabs G s) g), smul_inv_smul]
    exact hy
  obtain ⟨c', hc's, hc'y⟩ := hA.edge _ _ hy'
  rw [hA.type_std] at hc's
  have hc : c'⁻¹ ∈ stabs G s i := by
    show c'⁻¹ ∈ MulAction.stabilizer G (s i)
    rw [MulAction.mem_stabilizer_iff, inv_smul_eq_iff, hc's]
  refine ⟨mkHat (τ ((amEval (stabs G s) g)⁻¹ • y)) (g * amOf (stabs G s) i ⟨c'⁻¹, hc⟩),
    ⟨?_, g * amOf (stabs G s) i ⟨c'⁻¹, hc⟩, mkHat_mul_amOf i g _, rfl⟩, ?_⟩
  · intro hij
    exact hA.type_adj _ _ hy' (by rw [hA.type_std]; exact hij)
  · rw [hatProj_mk, map_mul, amEval_amOf, mul_smul]
    change amEval (stabs G s) g • c'⁻¹ • s (τ ((amEval (stabs G s) g)⁻¹ • y)) = y
    rw [← hc'y, inv_smul_smul, smul_inv_smul]

#audit_axioms hatLift_exists

/-- Neighbours of `(i, ĝ)` are `(j, ĝ â)` with `a ∈ P i`. -/
theorem hatAdj_mk_elim {i : Fin 3} {g : Am (stabs G s)} {w : Hat G s}
    (h : HatAdj G s (mkHat i g) w) :
    ∃ a : stabs G s i, i ≠ w.1 ∧ w = mkHat w.1 (g * amOf (stabs G s) i a) := by
  obtain ⟨hne, k, hk, hw⟩ := h
  change mkHat i k = mkHat i g at hk
  obtain ⟨c, hc⟩ := mkHat_eq_iff.mp hk
  have hk2 : g * amOf (stabs G s) i c⁻¹ = k := by
    rw [map_inv, hc, mul_inv_rev, inv_inv, mul_inv_cancel_left]
  exact ⟨c⁻¹, hne, by rw [hk2]; exact hw.symm⟩

#audit_axioms hatAdj_mk_elim

/-- Two neighbours of `(i, ĝ)` of the same type over the same vertex coincide. -/
theorem hatLift_coords (i j : Fin 3) (g : Am (stabs G s)) (a₁ a₂ : stabs G s i)
    (hp : (a₁ : G) • s j = (a₂ : G) • s j) :
    mkHat j (g * amOf (stabs G s) i a₁) = mkHat j (g * amOf (stabs G s) i a₂) := by
  have hb : ((a₁⁻¹ * a₂ : stabs G s i) : G) ∈ stabs G s j := by
    show ((a₁⁻¹ * a₂ : stabs G s i) : G) ∈ MulAction.stabilizer G (s j)
    rw [MulAction.mem_stabilizer_iff, Subgroup.coe_mul, Subgroup.coe_inv, mul_smul, ← hp,
      inv_smul_smul]
  rw [mkHat_eq_iff]
  have heq : (g * amOf (stabs G s) i a₁)⁻¹ * (g * amOf (stabs G s) i a₂) =
      amOf (stabs G s) i (a₁⁻¹ * a₂) := by
    rw [map_mul, map_inv, mul_inv_rev, mul_assoc, inv_mul_cancel_left]
  rw [heq, amOf_glue (stabs G s) (a := a₁⁻¹ * a₂) (b := ⟨_, hb⟩) rfl]
  exact ⟨_, rfl⟩

#audit_axioms hatLift_coords

/-- **Lifts of edges are unique.** -/
theorem hatLift_unique (hA : TriangleAction G Γ s τ) {i : Fin 3} {g : Am (stabs G s)}
    {w₁ w₂ : Hat G s} (h₁ : HatAdj G s (mkHat i g) w₁) (h₂ : HatAdj G s (mkHat i g) w₂)
    (hp : hatProj G s w₁ = hatProj G s w₂) : w₁ = w₂ := by
  have htype : w₁.1 = w₂.1 := by rw [← hatProj_type hA w₁, ← hatProj_type hA w₂, hp]
  obtain ⟨a₁, -, hw₁⟩ := hatAdj_mk_elim h₁
  obtain ⟨a₂, -, hw₂⟩ := hatAdj_mk_elim h₂
  have hp' : amEval (stabs G s) (g * amOf (stabs G s) i a₁) • s w₁.1 =
      amEval (stabs G s) (g * amOf (stabs G s) i a₂) • s w₁.1 := by
    have h := hp
    rw [hw₁, hw₂, hatProj_mk, hatProj_mk, ← htype] at h
    exact h
  rw [map_mul, map_mul, amEval_amOf, amEval_amOf, mul_smul, mul_smul] at hp'
  rw [hw₁, hw₂, ← htype]
  exact hatLift_coords i w₁.1 g a₁ a₂ (smul_left_cancel _ hp')

#audit_axioms hatLift_unique

/-- **Triangles lift.** Two neighbours of `(i, ĝ)` over adjacent vertices are adjacent. -/
theorem hatLift_tri (hA : TriangleAction G Γ s τ) {i : Fin 3} {g : Am (stabs G s)}
    {w₁ w₂ : Hat G s} (h₁ : HatAdj G s (mkHat i g) w₁) (h₂ : HatAdj G s (mkHat i g) w₂)
    (h : Γ.Adj (hatProj G s w₁) (hatProj G s w₂)) : HatAdj G s w₁ w₂ := by
  set e := amEval (stabs G s) g with he
  have hx₁ : Γ.Adj (s i) (e⁻¹ • hatProj G s w₁) := by
    have h' := hatProj_adj hA h₁
    rw [hatProj_mk, ← he] at h'
    rw [← hA.adj_smul e, smul_inv_smul]
    exact h'
  have hx₂ : Γ.Adj (s i) (e⁻¹ • hatProj G s w₂) := by
    have h' := hatProj_adj hA h₂
    rw [hatProj_mk, ← he] at h'
    rw [← hA.adj_smul e, smul_inv_smul]
    exact h'
  have hyz : Γ.Adj (e⁻¹ • hatProj G s w₁) (e⁻¹ • hatProj G s w₂) := (hA.adj_smul _ _ _).mpr h
  obtain ⟨c', hcx, hcy, hcz⟩ := hA.chamber _ _ _ hx₁ hyz hx₂
  rw [hA.type_std] at hcx
  have hc : c'⁻¹ ∈ stabs G s i := by
    show c'⁻¹ ∈ MulAction.stabilizer G (s i)
    rw [MulAction.mem_stabilizer_iff, inv_smul_eq_iff, hcx]
  set k := g * amOf (stabs G s) i ⟨c'⁻¹, hc⟩ with hk
  have hproj : ∀ (w : Hat G s), c' • e⁻¹ • hatProj G s w = s (τ (e⁻¹ • hatProj G s w)) →
      hatProj G s (mkHat (τ (e⁻¹ • hatProj G s w)) k) = hatProj G s w := by
    intro w hw
    rw [hatProj_mk, hk, map_mul, amEval_amOf, mul_smul, ← he]
    change e • c'⁻¹ • s (τ (e⁻¹ • hatProj G s w)) = hatProj G s w
    rw [← hw, inv_smul_smul, smul_inv_smul]
  have hadj : ∀ (w : Hat G s), HatAdj G s (mkHat i g) w →
      HatAdj G s (mkHat i g) (mkHat (τ (e⁻¹ • hatProj G s w)) k) := by
    intro w hw
    refine ⟨?_, k, mkHat_mul_amOf i g _, rfl⟩
    change i ≠ τ (e⁻¹ • hatProj G s w)
    rw [hA.type_smul, hatProj_type hA w]
    exact (hatAdj_mk_elim hw).choose_spec.1
  have hw₁ := hatLift_unique hA h₁ (hadj w₁ h₁) (hproj w₁ hcy).symm
  have hw₂ := hatLift_unique hA h₂ (hadj w₂ h₂) (hproj w₂ hcz).symm
  rw [hw₁, hw₂]
  refine ⟨?_, k, rfl, rfl⟩
  change τ (e⁻¹ • hatProj G s w₁) ≠ τ (e⁻¹ • hatProj G s w₂)
  exact hA.type_adj _ _ hyz

#audit_axioms hatLift_tri

end Develop

end BTri
end BooneHigmanLinear
end GroupApproximation
