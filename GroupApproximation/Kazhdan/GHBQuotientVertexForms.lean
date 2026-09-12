import Mathlib.GroupTheory.OrderOfElement
import GroupApproximation.Algebra.GroupTorsionFree
import GroupApproximation.Kazhdan.CCKWFiniteSubgroupsStatement
import GroupApproximation.Kazhdan.GHBQuotientVertexFamilies

/-!
# The quotient `ψ : GHB(7) → GL₄(F₇)` on the three vertex groups

`Kazhdan/GHBQuotientVertexFamilies.lean` shows that the subgroups `⟨V'a,V'b⟩`,
`⟨V'c,V'b⟩`, `⟨V'c,V'a⟩` of `GL₄(F₇)` have exponent seven and at least `7³`, `7⁴`, `7⁴`
elements.  They are the images under `ψ` of the vertex groups `⟨a,b⟩`, `⟨c,b⟩`, `⟨c,a⟩`
of `GHB(7)`.  This module draws the consequences the lattice route needs.

**Injectivity on the vertex groups.**  `U₃(7) → GHB(7) → GL₄(F₇)` has image `⟨V'a,V'b⟩`,
so it is injective once `|U₃(7)| ≤ 7³` (CCKW Proposition 7.2); likewise for `U₄(7)` twice.
So `ψ` kills no nontrivial element of a vertex group.

**Consequences.**  Over CCKW Theorem 3.1(ii) in its cyclic case
(`CCKWFiniteOrderConjugateIntoVertex`):
* `psiKer` is torsion-free (`isPowerTorsionFree_psiKer`): a torsion element of the
  kernel is conjugate into a vertex group, where `ψ` is injective;
* `GHB(7)` is infinite (`infinite_ghb7`): otherwise `abc` has finite order, so a
  conjugate of it lies in a vertex group, whose image has exponent seven, while
  `(V'a V'b V'c)⁷ ≠ 1` (the product has order `42`).  This half does not use the order
  bounds of the vertex groups;
* `psiKer` is infinite, being of finite index in `GHB(7)`.
-/

namespace GroupApproximation
namespace KMSGroup
namespace GHBQuotient

/-! ## Conjugation -/

theorem pow_eq_one_of_conj_pow_eq_one {G : Type*} [Group G] {x g : G} {n : ℕ}
    (h : (x⁻¹ * g * x) ^ n = 1) : g ^ n = 1 := by
  have h' : (x⁻¹ * g * x⁻¹⁻¹) ^ n = 1 := by simpa only [inv_inv] using h
  rw [conj_pow] at h'
  exact conj_eq_one_iff.mp h'

theorem eq_one_of_conj_eq_one {G : Type*} [Group G] {x g : G} (h : x⁻¹ * g * x = 1) :
    g = 1 := by
  have h' : x⁻¹ * g * x⁻¹⁻¹ = 1 := by simpa only [inv_inv] using h
  exact conj_eq_one_iff.mp h'

/-! ## The images of the vertex groups -/

theorem psi_mem_closure_ab {h : GHB 7} (hh : h ∈ Subgroup.closure {a 7, b 7}) :
    psi h ∈ Subgroup.closure ({uA, uB} : Set GL4) := by
  have h' := Subgroup.mem_map_of_mem psi hh
  rwa [MonoidHom.map_closure, Set.image_pair, psi_a, psi_b] at h'

theorem psi_mem_closure_cb {h : GHB 7} (hh : h ∈ Subgroup.closure {c 7, b 7}) :
    psi h ∈ Subgroup.closure ({uC, uB} : Set GL4) := by
  have h' := Subgroup.mem_map_of_mem psi hh
  rwa [MonoidHom.map_closure, Set.image_pair, psi_c, psi_b] at h'

theorem psi_mem_closure_ca {h : GHB 7} (hh : h ∈ Subgroup.closure {c 7, a 7}) :
    psi h ∈ Subgroup.closure ({uC, uA} : Set GL4) := by
  have h' := Subgroup.mem_map_of_mem psi hh
  rwa [MonoidHom.map_closure, Set.image_pair, psi_c, psi_a] at h'

/-- **The image of every vertex group has exponent seven.** -/
theorem psi_pow_seven_of_mem_vertex {h : GHB 7}
    (hh : h ∈ Subgroup.closure {a 7, b 7} ∨ h ∈ Subgroup.closure {c 7, b 7} ∨
      h ∈ Subgroup.closure {c 7, a 7}) : psi h ^ 7 = 1 := by
  rcases hh with hh | hh | hh
  · exact pow_seven_of_mem_closure_ab (psi_mem_closure_ab hh)
  · exact pow_seven_of_mem_closure_cb (psi_mem_closure_cb hh)
  · exact pow_seven_of_mem_closure_ca (psi_mem_closure_ca hh)

/-- `(V'a V'b V'c)⁷ ≠ 1`: the product has order `42`. -/
theorem uABC_pow_seven_ne_one : (uA * uB * uC) ^ 7 ≠ 1 := by decide +kernel

/-- **`GHB(7)` is infinite**, over CCKW Theorem 3.1(ii) in its cyclic case. -/
theorem infinite_ghb7 (hconj : CCKWFiniteOrderConjugateIntoVertex) : Infinite (GHB 7) := by
  by_contra hinf
  have hfin : Finite (GHB 7) := not_infinite_iff_finite.mp hinf
  obtain ⟨x, hx⟩ := hconj (a 7 * b 7 * c 7) (isOfFinOrder_of_finite _)
  have h7 := psi_pow_seven_of_mem_vertex hx
  have hmap : psi (x⁻¹ * (a 7 * b 7 * c 7) * x) = (psi x)⁻¹ * (uA * uB * uC) * psi x := by
    simp only [map_mul, map_inv, psi_a, psi_b, psi_c]
  rw [hmap] at h7
  exact uABC_pow_seven_ne_one (pow_eq_one_of_conj_pow_eq_one h7)

/-! ## Injectivity on the vertex groups, from the order bounds -/

theorem range_psi_comp_u3ToAB :
    (psi.comp (u3ToAB 7)).range = Subgroup.closure ({uA, uB} : Set GL4) := by
  rw [MonoidHom.range_comp, range_u3ToAB, MonoidHom.map_closure, Set.image_pair, psi_a, psi_b]

theorem range_psi_comp_u4ToCB :
    (psi.comp (u4ToCB 7)).range = Subgroup.closure ({uC, uB} : Set GL4) := by
  rw [MonoidHom.range_comp, range_u4ToCB, MonoidHom.map_closure, Set.image_pair, psi_c, psi_b]

theorem range_psi_comp_u4ToCA :
    (psi.comp (u4ToCA 7)).range = Subgroup.closure ({uC, uA} : Set GL4) := by
  rw [MonoidHom.range_comp, range_u4ToCA, MonoidHom.map_closure, Set.image_pair, psi_c, psi_a]

/-- A homomorphism out of a finite group whose range is at least as large is injective. -/
theorem injective_of_nat_card_le_range {H G : Type*} [Group H] [Group G] [Finite H]
    (f : H →* G) (hcard : Nat.card H ≤ Nat.card f.range) : Function.Injective f := by
  have hbij := f.rangeRestrict_surjective.bijective_of_nat_card_le hcard
  intro x y hxy
  exact hbij.1 (Subtype.ext hxy)

theorem injective_psi_comp_u3ToAB [Finite (U3 7)] (hcard : Nat.card (U3 7) ≤ 7 ^ 3) :
    Function.Injective (psi.comp (u3ToAB 7)) := by
  refine injective_of_nat_card_le_range _ (hcard.trans ?_)
  rw [range_psi_comp_u3ToAB]
  exact card_closure_ab

theorem injective_psi_comp_u4ToCB [Finite (U4 7)] (hcard : Nat.card (U4 7) ≤ 7 ^ 4) :
    Function.Injective (psi.comp (u4ToCB 7)) := by
  refine injective_of_nat_card_le_range _ (hcard.trans ?_)
  rw [range_psi_comp_u4ToCB]
  exact card_closure_cb

theorem injective_psi_comp_u4ToCA [Finite (U4 7)] (hcard : Nat.card (U4 7) ≤ 7 ^ 4) :
    Function.Injective (psi.comp (u4ToCA 7)) := by
  refine injective_of_nat_card_le_range _ (hcard.trans ?_)
  rw [range_psi_comp_u4ToCA]
  exact card_closure_ca

/-- **`ψ` kills no nontrivial element of a vertex group**, over the order bounds. -/
theorem eq_one_of_mem_vertex_of_psi_eq_one [Finite (U3 7)] [Finite (U4 7)]
    (h3 : Nat.card (U3 7) ≤ 7 ^ 3) (h4 : Nat.card (U4 7) ≤ 7 ^ 4) {h : GHB 7}
    (hh : h ∈ Subgroup.closure {a 7, b 7} ∨ h ∈ Subgroup.closure {c 7, b 7} ∨
      h ∈ Subgroup.closure {c 7, a 7}) (h1 : psi h = 1) : h = 1 := by
  rcases hh with hh | hh | hh
  · rw [← range_u3ToAB] at hh
    obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hh
    have hy : y = 1 := injective_psi_comp_u3ToAB h3 (by simpa using h1)
    simp [hy]
  · rw [← range_u4ToCB] at hh
    obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hh
    have hy : y = 1 := injective_psi_comp_u4ToCB h4 (by simpa using h1)
    simp [hy]
  · rw [← range_u4ToCA] at hh
    obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hh
    have hy : y = 1 := injective_psi_comp_u4ToCA h4 (by simpa using h1)
    simp [hy]

/-! ## The kernel of `ψ` -/

/-- **`psiKer` is torsion-free**, over CCKW Theorem 3.1(ii) (cyclic case) and the order
bounds of the vertex groups. -/
theorem isPowerTorsionFree_psiKer (hconj : CCKWFiniteOrderConjugateIntoVertex)
    [Finite (U3 7)] [Finite (U4 7)] (h3 : Nat.card (U3 7) ≤ 7 ^ 3)
    (h4 : Nat.card (U4 7) ≤ 7 ^ 4) : IsPowerTorsionFree ↥psiKer := by
  intro g n hn hgn
  have hgn' : (g : GHB 7) ^ n = 1 := by
    simpa using congrArg Subtype.val hgn
  obtain ⟨x, hx⟩ := hconj (g : GHB 7) (isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, hgn'⟩)
  have hg1 : psi (g : GHB 7) = 1 := MonoidHom.mem_ker.mp g.2
  have hpsi : psi (x⁻¹ * (g : GHB 7) * x) = 1 := by
    simp only [map_mul, map_inv, hg1, mul_one, inv_mul_cancel]
  exact Subtype.ext (eq_one_of_conj_eq_one (eq_one_of_mem_vertex_of_psi_eq_one h3 h4 hx hpsi))

/-- **`psiKer` is infinite**, being of finite index in the infinite group `GHB(7)`. -/
theorem infinite_psiKer (hconj : CCKWFiniteOrderConjugateIntoVertex) : Infinite ↥psiKer := by
  haveI := infinite_ghb7 hconj
  by_contra hinf
  have hfin : Finite ↥psiKer := not_infinite_iff_finite.mp hinf
  have h := Subgroup.card_mul_index psiKer
  rw [Nat.card_eq_zero_of_infinite (α := GHB 7)] at h
  have hS : Nat.card ↥psiKer ≠ 0 := Nat.card_ne_zero.mpr ⟨inferInstance, hfin⟩
  exact mul_ne_zero hS psiKer_finiteIndex.index_ne_zero h

end GHBQuotient
end KMSGroup
end GroupApproximation

#audit_axioms GroupApproximation.KMSGroup.GHBQuotient.uABC_pow_seven_ne_one
#audit_axioms GroupApproximation.KMSGroup.GHBQuotient.psi_pow_seven_of_mem_vertex
#audit_axioms GroupApproximation.KMSGroup.GHBQuotient.infinite_ghb7
#audit_axioms GroupApproximation.KMSGroup.GHBQuotient.eq_one_of_mem_vertex_of_psi_eq_one
#audit_axioms GroupApproximation.KMSGroup.GHBQuotient.isPowerTorsionFree_psiKer
#audit_axioms GroupApproximation.KMSGroup.GHBQuotient.infinite_psiKer
