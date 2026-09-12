import GroupApproximation.Algebra.ProductFinitePresentation
import GroupApproximation.GroupTheory.CasingPair
import GroupApproximation.Meta.AxiomGuard

/-!
# Products of commuting subgroups and casing pairs inside a subgroup

Hyde–Lodha, proof of Proposition 4.7: "Let `R = ∏ Rstab_{Γ_n}(L_j)` and `R_1 = ∏ Rstab_Γ(L_j)`.
From our hypothesis, `R' ⊆ R_1 ⊆ Γ_K ⊆ R`.  Now `R_1, R` are of type `F_∞` … So they form a casing
pair for `Γ_K`."  The factors have disjoint supports, so they commute and meet trivially.

* `isFinitelyPresented_sup_of_commute`: for elementwise commuting subgroups `A, B` with `A ⊓ B = ⊥`,
  `A ⊔ B ≅ A × B`, so it is finitely presented when `A` and `B` are;
* `isFinitelyPresented_of_commutator_le`: the casing-pair lemma for `N ≤ H ≤ K` inside a subgroup `K`
  with `K' ≤ N`;
* `commutator_sup_le_of_commute`: `(A ⊔ B)' ≤ N` when `A' ≤ N`, `B' ≤ N` and `A, B` commute.
-/

namespace GroupApproximation
namespace HydeLodha

open scoped commutatorElement

/-- The multiplication map `A × B → G` of two elementwise commuting subgroups. -/
def commuteSupHom {G : Type*} [Group G] (A B : Subgroup G)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, Commute a b) : ↥A × ↥B →* G :=
  MonoidHom.noncommCoprod A.subtype B.subtype fun a b => hcomm a a.2 b b.2

theorem commuteSupHom_apply {G : Type*} [Group G] (A B : Subgroup G)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, Commute a b) (p : ↥A × ↥B) :
    commuteSupHom A B hcomm p = (p.1 : G) * p.2 := rfl

theorem range_commuteSupHom {G : Type*} [Group G] (A B : Subgroup G)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, Commute a b) : (commuteSupHom A B hcomm).range = A ⊔ B := by
  refine le_antisymm (fun x hx => ?_) (sup_le (fun a ha => ?_) (fun b hb => ?_))
  · obtain ⟨p, rfl⟩ := MonoidHom.mem_range.mp hx
    rw [commuteSupHom_apply]
    exact (A ⊔ B).mul_mem (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)
  · exact MonoidHom.mem_range.mpr ⟨(⟨a, ha⟩, 1), by simp [commuteSupHom_apply]⟩
  · exact MonoidHom.mem_range.mpr ⟨(1, ⟨b, hb⟩), by simp [commuteSupHom_apply]⟩

theorem commuteSupHom_injective {G : Type*} [Group G] (A B : Subgroup G)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, Commute a b) (hdisj : A ⊓ B = ⊥) :
    Function.Injective (commuteSupHom A B hcomm) := by
  rw [injective_iff_map_eq_one]
  intro p h
  rw [commuteSupHom_apply] at h
  have hab : (p.1 : G) = (p.2 : G)⁻¹ := eq_inv_of_mul_eq_one_left h
  have hmem : (p.1 : G) ∈ A ⊓ B :=
    Subgroup.mem_inf.mpr ⟨p.1.2, by rw [hab]; exact B.inv_mem p.2.2⟩
  rw [hdisj, Subgroup.mem_bot] at hmem
  have hb : (p.2 : G) = 1 := by
    rw [hmem, one_mul] at h
    exact h
  exact Prod.ext (Subtype.ext hmem) (Subtype.ext hb)

/-- **`A ⊔ B ≅ A × B` is finitely presented.** -/
theorem isFinitelyPresented_sup_of_commute {G : Type*} [Group G] (A B : Subgroup G)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, Commute a b) (hdisj : A ⊓ B = ⊥)
    [Group.IsFinitelyPresented ↥A] [Group.IsFinitelyPresented ↥B] :
    Group.IsFinitelyPresented ↥(A ⊔ B) :=
  Group.IsFinitelyPresented.equiv
    ((MonoidHom.ofInjective (commuteSupHom_injective A B hcomm hdisj)).trans
      (MulEquiv.subgroupCongr (range_commuteSupHom A B hcomm)))

/-- **Casing pairs inside a subgroup.**  `N ≤ H ≤ K` with `K' ≤ N`, `K` finitely generated and `N`
finitely presented. -/
theorem isFinitelyPresented_of_commutator_le {G : Type*} [Group G] (N H K : Subgroup G)
    (hNH : N ≤ H) (hHK : H ≤ K) (hKN : ⁅K, K⁆ ≤ N) [Group.FG ↥K]
    [Group.IsFinitelyPresented ↥N] : Group.IsFinitelyPresented ↥H := by
  haveI : Group.IsFinitelyPresented ↥(N.subgroupOf K) :=
    Group.IsFinitelyPresented.equiv (Subgroup.subgroupOfEquivOfLe (hNH.trans hHK)).symm
  haveI : Group.IsFinitelyPresented ↥(H.subgroupOf K) := by
    refine CasingPair.isFinitelyPresented_of_casingPair (N.subgroupOf K) (H.subgroupOf K)
      (fun x hx => Subgroup.mem_subgroupOf.mpr (hNH (Subgroup.mem_subgroupOf.mp hx))) ?_
    rw [Subgroup.commutator_le]
    intro x _ y _
    rw [Subgroup.mem_subgroupOf]
    have e : ((⁅x, y⁆ : ↥K) : G) = ⁅(x : G), (y : G)⁆ := map_commutatorElement K.subtype x y
    rw [e]
    exact hKN (Subgroup.commutator_mem_commutator x.2 y.2)
  exact Group.IsFinitelyPresented.equiv (Subgroup.subgroupOfEquivOfLe hHK)

/-- **`(A ⊔ B)' ≤ N`** for elementwise commuting `A, B` with `A' ≤ N` and `B' ≤ N`:
`⁅a₁ b₁, a₂ b₂⁆ = ⁅a₁, a₂⁆ ⁅b₁, b₂⁆`. -/
theorem commutator_sup_le_of_commute {G : Type*} [Group G] (A B N : Subgroup G)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, Commute a b) (hA : ⁅A, A⁆ ≤ N) (hB : ⁅B, B⁆ ≤ N) :
    ⁅A ⊔ B, A ⊔ B⁆ ≤ N := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [← range_commuteSupHom A B hcomm] at hx hy
  obtain ⟨p, rfl⟩ := MonoidHom.mem_range.mp hx
  obtain ⟨q, rfl⟩ := MonoidHom.mem_range.mp hy
  rw [← map_commutatorElement (commuteSupHom A B hcomm) p q, commuteSupHom_apply]
  have e1 : (((⁅p, q⁆ : ↥A × ↥B).1 : ↥A) : G) = ⁅((p.1 : ↥A) : G), ((q.1 : ↥A) : G)⁆ :=
    map_commutatorElement (A.subtype.comp (MonoidHom.fst ↥A ↥B)) p q
  have e2 : (((⁅p, q⁆ : ↥A × ↥B).2 : ↥B) : G) = ⁅((p.2 : ↥B) : G), ((q.2 : ↥B) : G)⁆ :=
    map_commutatorElement (B.subtype.comp (MonoidHom.snd ↥A ↥B)) p q
  rw [e1, e2]
  exact N.mul_mem (hA (Subgroup.commutator_mem_commutator p.1.2 q.1.2))
    (hB (Subgroup.commutator_mem_commutator p.2.2 q.2.2))

#audit_axioms GroupApproximation.HydeLodha.isFinitelyPresented_sup_of_commute
#audit_axioms GroupApproximation.HydeLodha.isFinitelyPresented_of_commutator_le
#audit_axioms GroupApproximation.HydeLodha.commutator_sup_le_of_commute

end HydeLodha
end GroupApproximation
