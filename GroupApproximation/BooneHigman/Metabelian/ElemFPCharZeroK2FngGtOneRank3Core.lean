import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2FngGtOneRank3Map
import GroupApproximation.Meta.AxiomGuard

/-!
# The section method for `K₂(3, S)` over a coefficient map (lane `bh-met-93s`, part 4)

Fix a coefficient map `φ : R → S` of commutative rings, `Φ = ringMap φ : St_3(R) → St_3(S)`
and a finite `s ⊆ K₂(3, S)`.  Put `N = ⟪Φ(K₂(3, R)) ∪ s⟫` and `Q = Φ(St_3(R)) ⊔ N`.
Let `E_3(S)` act on a type `X`, and let `St_3(S)` act on `X` through `projection`.  For a map
`σ : X → St_3(S)`, the **check** of `g ∈ St_3(S)` is: for every `y : X`,

  `σ(g · y)⁻¹ · g · σ(y) ∈ Q`.

**Proved outright.**
* `czK2FngGtOneRank3_good`: the elements passing the check form a subgroup.
* `czK2FngGtOneRank3_mem_Q_of_top`: if every element passes the check and `σ(y₀) ∈ Q`, then
  `K₂(3, S) ⊆ Q`.  (`K₂` acts trivially on `X`.)
* `czK2FngGtOneRank3_mem_N_of_mem_Q`: if `φ` is injective, then `Q ∩ K₂(3, S) ⊆ N`.
* `czK2FngGtOneRank3_mem_Q_of_projection`: if `K₂(3, S) ≤ N`, then every `g` with
  `projection g ∈ E_3(φ)(E_3(R))` lies in `Q`.  This is used only for the converse direction.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup

section Core

variable {R S : Type*} [CommRing R] [CommRing S]

/-- `N = ⟪Φ(K₂(3, R)) ∪ s⟫`. -/
def czK2FngGtOneRank3_N (φ : R →+* S) (s : Set (SteinbergGroup (Fin 3) S)) :
    Subgroup (SteinbergGroup (Fin 3) S) :=
  Subgroup.normalClosure
    (ringMap φ '' (K2 (Fin 3) R : Set (SteinbergGroup (Fin 3) R)) ∪ s)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngGtOneRank3_N

/-- `Q = Φ(St_3(R)) ⊔ N`. -/
def czK2FngGtOneRank3_Q (φ : R →+* S) (s : Set (SteinbergGroup (Fin 3) S)) :
    Subgroup (SteinbergGroup (Fin 3) S) :=
  (ringMap (I := Fin 3) φ).range ⊔ czK2FngGtOneRank3_N φ s

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngGtOneRank3_Q

/-- The check of `g` against the section `σ`: `σ(g · y)⁻¹ · g · σ(y) ∈ Q` for every `y`. -/
def czK2FngGtOneRank3_Check {X : Type*} [MulAction (elementaryGroup (Fin 3) S) X]
    (Q : Subgroup (SteinbergGroup (Fin 3) S)) (σ : X → SteinbergGroup (Fin 3) S)
    (g : SteinbergGroup (Fin 3) S) : Prop :=
  ∀ y : X, (σ (projection g • y))⁻¹ * g * σ y ∈ Q

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngGtOneRank3_Check

/-- The elements passing the check form a subgroup. -/
def czK2FngGtOneRank3_good {X : Type*} [MulAction (elementaryGroup (Fin 3) S) X]
    (Q : Subgroup (SteinbergGroup (Fin 3) S)) (σ : X → SteinbergGroup (Fin 3) S) :
    Subgroup (SteinbergGroup (Fin 3) S) where
  carrier := {g | czK2FngGtOneRank3_Check Q σ g}
  one_mem' := by
    intro y
    rw [map_one, one_smul, mul_one, inv_mul_cancel]
    exact Q.one_mem
  mul_mem' := by
    intro a b ha hb y
    have e : (σ (projection a • projection b • y))⁻¹ * (a * b) * σ y =
        ((σ (projection a • projection b • y))⁻¹ * a * σ (projection b • y)) *
          ((σ (projection b • y))⁻¹ * b * σ y) := by
      group
    rw [map_mul, mul_smul, e]
    exact Q.mul_mem (ha (projection b • y)) (hb y)
  inv_mem' := by
    intro a ha y
    have hy : projection a • projection a⁻¹ • y = y := by
      rw [← mul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]
    have h := Q.inv_mem (ha (projection a⁻¹ • y))
    rw [hy] at h
    have e : ((σ y)⁻¹ * a * σ (projection a⁻¹ • y))⁻¹ =
        (σ (projection a⁻¹ • y))⁻¹ * a⁻¹ * σ y := by
      group
    rw [e] at h
    exact h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngGtOneRank3_good

theorem czK2FngGtOneRank3_mem_good {X : Type*} [MulAction (elementaryGroup (Fin 3) S) X]
    {Q : Subgroup (SteinbergGroup (Fin 3) S)} {σ : X → SteinbergGroup (Fin 3) S}
    {g : SteinbergGroup (Fin 3) S} :
    g ∈ czK2FngGtOneRank3_good Q σ ↔ czK2FngGtOneRank3_Check Q σ g :=
  Iff.rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngGtOneRank3_mem_good

/-- If every element passes the check and `σ(y₀) ∈ Q`, then `K₂(3, S) ⊆ Q`. -/
theorem czK2FngGtOneRank3_mem_Q_of_top {X : Type*} [MulAction (elementaryGroup (Fin 3) S) X]
    (Q : Subgroup (SteinbergGroup (Fin 3) S)) (σ : X → SteinbergGroup (Fin 3) S) (y₀ : X)
    (h0 : σ y₀ ∈ Q) (htop : czK2FngGtOneRank3_good Q σ = ⊤)
    {k : SteinbergGroup (Fin 3) S} (hk : k ∈ K2 (Fin 3) S) : k ∈ Q := by
  have hg : k ∈ czK2FngGtOneRank3_good Q σ := by
    rw [htop]
    exact Subgroup.mem_top k
  have h : (σ (projection k • y₀))⁻¹ * k * σ y₀ ∈ Q := czK2FngGtOneRank3_mem_good.mp hg y₀
  rw [(mem_K2_iff k).mp hk, one_smul] at h
  have e : k = σ y₀ * ((σ y₀)⁻¹ * k * σ y₀) * (σ y₀)⁻¹ := by
    group
  rw [e]
  exact Q.mul_mem (Q.mul_mem h0 h) (Q.inv_mem h0)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngGtOneRank3_mem_Q_of_top

end Core

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
